//! `tzdata` uses the IANA Time Zone Database to provide conversion between timezones.
extern crate time;

mod parse;

pub use time::*;
use std::rc::Rc;
use std::io;
use std::fmt;
use std::cmp::{Eq, PartialEq, Ord, PartialOrd, Ordering};

/// A named timezone from the [`IANA Time Zone Database`](https://www.iana.org/time-zones)
///
/// # Example
///
/// ```rust
/// let utc = tzdata::Timezone::utc();
/// let now = utc.now();
///
/// for tzname in &["Europe/Paris", "America/New_York", "Asia/Seoul"] {
///     let tz = tzdata::Timezone::new(tzname).unwrap();
///     let now = now.project(&tz);
///     println!("it is now {:?} in {}", now, tz.name);
/// }
/// ```
pub struct Timezone {
    /// The timezone name e.g. `Europe/Paris`.
    pub name: String,
    /// The UTC offset transitions
    trans: Vec<Transition>,
}

#[derive(Debug)]
struct Transition {
    utc: i64,
    ttype: Rc<Type>,
}

#[derive(Debug)]
struct Type {
    utc_off_sec: i32,
    is_dst: bool,
    abbr: String,
}

impl Timezone {
    /// Try to load a new `Timezone`.
    /// It assumes that the zoneinfo data are located
    /// under `/usr/share/zoneinfo`.
    pub fn new(timezone: &str) -> io::Result<Self> {
        parse::load_timezone(timezone)
    }

    /// Load the local `Timezone` set by the system,
    /// disregarding the `TZ` environment variable.
    pub fn local() -> io::Result<Self> {
        parse::load_timezone("localtime")
    }

    /// Returns the `UTC` timezone.
    pub fn utc() -> Self {
        Self::fixed(0)
    }

    /// Returns a fixed offset to `UTC` timezone.
    /// The provided offset is in seconds.
    pub fn fixed(sec: i32) -> Self {
        Timezone {
            name: "UTC".to_owned(),
            trans: vec![
                Transition {
                    utc: std::i64::MIN,
                    ttype: Rc::new(Type {
                        utc_off_sec: sec,
                        is_dst: false,
                        abbr: "".to_owned(),
                    }),
                }
            ],
        }
    }

    /// Compute the UTC offset in this `Timezone` for unix timestamp `t`.
    fn offset(&self, stamp: i64) -> i32 {
        let idx = match self.trans.binary_search_by(|t| t.utc.cmp(&stamp)) {
            Err(0) => return 0, // FIXME?
            Err(i) => i - 1,
            Ok(i) => i,
        };

        self.trans[idx].ttype.utc_off_sec
    }

    /// Return the `Datetime` representing now, relative to this `Timezone`.
    pub fn now(&self) -> Datetime {
        Datetime {
            tz: self,
            stamp: time::get_time(),
            is_60th_sec: false,
        }
    }

    /// Create a new `Datetime` relative to this `Timezone`.
    /// Panics if the following constraints do not hold:
    ///
    /// - `month` ∊ [1, 12]
    /// - `day` ∊ [1, 31] and is valid within the month
    /// - `hour` ∊ [0, 23]
    /// - `minute` ∊ [0, 59]
    /// - `second` ∊ [0, 59]
    /// - `nano` ∊ [0, 999999999]
    pub fn datetime(&self, year: i32, month: i32, day: i32, hour: i32, minute: i32, second: i32, nano: i32) -> Datetime {
        let is_leap_year = (year % 4 == 0 && year % 100 != 0) || year % 400 == 0;

        // Panics if constaints described in documentation do not hold.
        assert!(month >= 1 && month <= 12);
        assert!(hour <= 23);
        assert!(minute <= 59);
        assert!(second <= 59); // TODO: handle leap second
        assert!(nano <= 999_999_999);
        let max_day = match month {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
            4 | 6 | 9 | 11 => 30,
            2 if is_leap_year => 30,
            2 => 29,
            _ => unreachable!(),
        };
        assert!(day >= 1 && day <= max_day);

        // Let the time crate do the heavy lifting.
        let utc_dt = time::Tm {
            tm_sec: second as i32,
            tm_min: minute as i32,
            tm_hour: hour as i32,
            tm_mday: day as i32,
            tm_mon: (month - 1) as i32,
            tm_year: (year - 1900) as i32,
            tm_wday: 0,
            tm_yday: 0,
            tm_isdst: 0,
            tm_utcoff: 0,
            tm_nsec: nano as i32,
        };
        let mut stamp = utc_dt.to_timespec();
        let utc_offset = self.offset(stamp.sec);
        stamp.sec -= utc_offset as i64;

        println!("stamp: {}", stamp.sec);
        Datetime {
            tz: self,
            stamp: stamp,
            is_60th_sec: false, // Always false because of ambiguity
        }
    }
}

/// A precise point in time along associated to a `Timezone`.
///
/// The `Datetime` cannot be created on its own as it depends on
/// a `Timezone`. `tzdata` does not expose a naive flavor of Datetime.
/// To build a `Datetime`, instanciate a `Timezone` first and call
/// the desired method.
///
/// ```rust
/// let paris = tzdata::Timezone::new("Europe/Paris").unwrap();
/// let midnight_in_paris = paris.datetime(2015, 12, 25, 0, 0, 0, 0);
///
/// let utc = tzdata::Timezone::utc();
/// let t = midnight_in_paris.project(&utc);
///
/// assert_eq!(t.date(), (2015, 12, 24));
/// assert_eq!(t.time(), (23, 0, 0, 0));
/// ```
pub struct Datetime<'a> {
    /// The associated timezone.
    tz: &'a Timezone,
    /// The offset since Unix Epoch. This is *not* the number
    /// of SI seconds since Unix Epoch because of leap seconds.
    stamp: time::Timespec,
    /// Remove ambiguous datetime on leap. When stamp
    /// corresponds to a leap second, use this field
    /// to know whether the `Datetime` corresponds to
    /// the 59th or the 60th second.
    is_60th_sec: bool,
}

impl<'a> Datetime<'a> {
    /// Project the current `Datetime` in another `Timezone`.
    pub fn project<'b>(&self, tz: &'b Timezone) -> Datetime<'b> {
        Datetime {
            tz: tz,
            stamp: self.stamp,
            is_60th_sec: self.is_60th_sec,
        }
    }

    /// Return the tm in the associated `Timezone`.
    fn tm(&self) -> time::Tm {
        let offset = self.tz.offset(self.stamp.sec);
        let local = time::Timespec {
            sec: self.stamp.sec + offset as i64,
            nsec: self.stamp.nsec,
        };
        let mut tm = time::at_utc(local);
        println!("on {:#?}, offset for {} = {}", tm, self.tz.name, offset);
        tm.tm_utcoff = offset;
        tm
    }

    /// Return the date component of the `Datetime` expressed
    /// in the associated `Timezone`. The tuple holds the
    /// year, month and day in this order.
    pub fn date(&self) -> (i32, i32, i32) {
        let tm = self.tm();
        (tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday)
    }

    /// Return the time component of the `Datetime` expressed
    /// in the associated `Timezone`. The tuple holds
    /// the hour, minute, second and nanosecond in this order.
    pub fn time(&self) -> (i32, i32, i32, i32) {
        let tm = self.tm();
        (tm.tm_hour, tm.tm_min, tm.tm_sec, tm.tm_nsec)
    }
}

impl<'a> PartialEq<Datetime<'a>> for Datetime<'a> {
    fn eq(&self, other: &Datetime) -> bool {
        self.stamp.eq(&other.stamp)
    }
}

impl<'a> Eq for Datetime<'a> {}

impl<'a> PartialOrd<Datetime<'a>> for Datetime<'a> {
    fn partial_cmp(&self, other: &Datetime) -> Option<Ordering> {
        let cmp = self.stamp.cmp(&other.stamp);
        if let Ordering::Equal = cmp {
            Some(self.is_60th_sec.cmp(&other.is_60th_sec))
        } else {
            Some(cmp)
        }
    }
}

impl<'a> Ord for Datetime<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<'a> fmt::Debug for Datetime<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", self.tm().rfc3339())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::time;

    #[test]
    fn test_datetime() {
        let utc = Timezone::utc();
        for &((y, m, d, h, mi, s, n), stamp) in &[
            ((1970, 1, 1, 0, 0, 0, 0), 0),
            ((1970, 1, 1, 1, 0, 0, 0), 3600),
            ((2016, 1, 1, 0, 0, 0, 0), 1451606400),
        ] {
            let stamp = time::Timespec {
                sec: stamp,
                nsec: 0,
            };
            let dt = utc.datetime(y, m, d, h, mi, s, n);
            assert_eq!(dt.stamp, stamp);
            assert_eq!(dt.is_60th_sec, false);
        }
    }

    #[test]
    fn test_tz_projection() {
        let utc = Timezone::utc();
        let seoul = Timezone::new("Asia/Seoul").unwrap();
        let new_york = Timezone::new("America/New_York").unwrap();

        let t = utc.datetime(2016, 1, 15, 20, 0, 0, 0);
        let t_seoul = t.project(&seoul);
        let t_ny = t.project(&new_york);

        assert_eq!(t.date(), (2016, 1, 15));
        assert_eq!(t.time(), (20, 0, 0, 0));
        assert_eq!(t_seoul, t);
        assert_eq!(t_seoul.date(), (2016, 1, 16));
        assert_eq!(t_seoul.time(), (5, 0, 0, 0));
        assert_eq!(t_ny, t);
        assert_eq!(t_ny.date(), (2016, 1, 15));
        assert_eq!(t_ny.time(), (15, 0, 0, 0));
    }
}

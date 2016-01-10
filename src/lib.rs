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
    off: i32,
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
            trans: vec![Transition {
                            utc: std::i64::MIN,
                            ttype: Rc::new(Type {
                                off: sec,
                                is_dst: false,
                                abbr: "".to_owned(),
                            }),
                        }],
        }
    }

    /// Compute the UTC offset in this `Timezone` for unix timestamp `t`.
    fn offset(&self, stamp: i64) -> &Type {
        let idx = match self.trans.binary_search_by(|t| t.utc.cmp(&stamp)) {
            Err(0) => unreachable!(),
            Err(i) => i - 1,
            Ok(i) => i,
        };

        &self.trans[idx].ttype
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
    pub fn datetime(&self,
                    year: i32,
                    month: i32,
                    day: i32,
                    hour: i32,
                    minute: i32,
                    second: i32,
                    nano: i32)
                    -> Datetime {
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
        let utc_offset = self.offset(stamp.sec).off;
        stamp.sec -= utc_offset as i64;

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
        let offset = self.tz.offset(self.stamp.sec).off;
        let local = time::Timespec {
            sec: self.stamp.sec + offset as i64,
            nsec: self.stamp.nsec,
        };
        let mut tm = time::at_utc(local);
        tm.tm_utcoff = offset;
        tm
    }

    /// Convert a tm to date.
    fn tm_to_date(tm: &time::Tm) -> (i32, i32, i32) {
        (tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday)
    }

    /// Convert a tm to time.
    fn tm_to_time(tm: &time::Tm) -> (i32, i32, i32, i32) {
        (tm.tm_hour, tm.tm_min, tm.tm_sec, tm.tm_nsec)
    }

    /// Convert a tm to weekday string.
    fn tm_to_weekday(tm: &time::Tm) -> &'static str {
        match tm.tm_wday {
            0 => "Sunday",
            1 => "Monday",
            2 => "Tuesday",
            3 => "Wednesday",
            4 => "Thursday",
            5 => "Friday",
            6 => "Saturday",
            _ => unreachable!(),
        }
    }

    /// Convert a tm to a month string.
    fn tm_to_month(tm: &time::Tm) -> &'static str {
        match tm.tm_mon {
            0 => "January",
            1 => "February",
            2 => "March",
            3 => "April",
            4 => "May",
            5 => "June",
            6 => "July",
            7 => "August",
            8 => "September",
            9 => "October",
            10 => "November",
            11 => "December",
            _ => unreachable!(),
        }
    }

    /// Return the date component of the `Datetime` expressed
    /// in the associated `Timezone`. The tuple holds the
    /// year, month and day in this order.
    pub fn date(&self) -> (i32, i32, i32) {
        let tm = self.tm();
        Self::tm_to_date(&tm)
    }

    /// Return the time component of the `Datetime` expressed
    /// in the associated `Timezone`. The tuple holds
    /// the hour, minute, second and nanosecond in this order.
    pub fn time(&self) -> (i32, i32, i32, i32) {
        let tm = self.tm();
        Self::tm_to_time(&tm)
    }

    /// Format the `Datetime` according to the provided `format`.
    /// The following control characters are implemented:
    ///
    /// - `%%`: the '%' character
    /// - `%Y`: year (2006)
    /// - `%m`: month (01)
    /// - `%d`: day of the month (02)
    /// - `%e`: day of the month (2)
    /// - `%H`: hour (15)
    /// - `%M`: minute (04)
    /// - `%S`: second (05)
    /// - `%3`: millisecond (123)
    /// - `%6`: microsecond (123456)
    /// - `%9`: nanosecond (123456789)
    /// - `%x`: UTC offset (+02:00 or -05:00)
    /// - `%z`: UTC offset (+0200 or -0500)
    /// - `%Z`: timezone abbreviation (CET)
    /// - `%w`: weekday (1)
    /// - `%a`: abbreviated weekday name (Mon)
    /// - `%A`: full weekday name (Monday)
    /// - `%b`: abbreviated month name (Jan)
    /// - `%B`: full month name (January)
    /// - `%C`: century (20)
    ///
    /// Panics if the format is invalid.
    pub fn format(&self, fmt: &str) -> String {
        use std::fmt::Write;

        let mut out = String::with_capacity(2 * fmt.len());

        let tm = self.tm();
        let date = Self::tm_to_date(&tm);
        let time = Self::tm_to_time(&tm);
        let off = self.tz.offset(self.stamp.sec);

        let mut chars = fmt.chars();
        loop {
            match chars.next() {
                None => break,
                Some('%') => {
                    match chars.next() {
                        None => panic!("Unfinished formatting after %"),
                        Some('%') => out.push('%'),
                        Some('Y') => write!(out, "{:04}", date.0).unwrap_or(()),
                        Some('m') => write!(out, "{:02}", date.1).unwrap_or(()),
                        Some('d') => write!(out, "{:02}", date.2).unwrap_or(()),
                        Some('e') => write!(out, "{}", date.2).unwrap_or(()),
                        Some('H') => write!(out, "{:02}", time.0).unwrap_or(()),
                        Some('M') => write!(out, "{:02}", time.1).unwrap_or(()),
                        Some('S') => write!(out, "{:02}", time.2).unwrap_or(()),
                        Some('3') => write!(out, "{:03}", time.3 / 1_000_000).unwrap_or(()),
                        Some('6') => write!(out, "{:06}", time.3 / 1_000).unwrap_or(()),
                        Some('9') => write!(out, "{:09}", time.3).unwrap_or(()),
                        Some('x') => {
                            write!(out, "{:+03}:{:02}", off.off / 3600, off.off % 3600 / 60)
                                .unwrap_or(())
                        }
                        Some('z') => {
                            write!(out, "{:+03}{:02}", off.off / 3600, off.off % 3600 / 60)
                                .unwrap_or(())
                        }
                        Some('Z') => write!(out, "{}", off.abbr).unwrap_or(()),
                        Some('w') => write!(out, "{}", tm.tm_wday).unwrap_or(()),
                        Some('a') => {
                            write!(out, "{}", &Self::tm_to_weekday(&tm)[..3]).unwrap_or(())
                        }
                        Some('A') => write!(out, "{}", Self::tm_to_weekday(&tm)).unwrap_or(()),
                        Some('b') => write!(out, "{}", &Self::tm_to_month(&tm)[..3]).unwrap_or(()),
                        Some('B') => write!(out, "{}", Self::tm_to_month(&tm)).unwrap_or(()),
                        Some('C') => write!(out, "{}", date.0 / 100).unwrap_or(()),
                        Some(c) => panic!("unknown format control %{}", c),
                    }
                }
                Some(c) => out.push(c),
            }
        }

        out
    }

    /// Format `Datetime` according to RFC 3339 format.
    pub fn rfc3339(&self) -> String {
        self.format("%Y-%m-%dT%H:%M:%S%x")
    }

    /// Format `Datetime` according to RFC 2822 format.
    pub fn rfc2822(&self) -> String {
        self.format("%a, %e %b %Y %H:%M:%S %z")
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
        for &((y, m, d, h, mi, s, n), stamp) in &[((1970, 1, 1, 0, 0, 0, 0), 0),
                                                  ((1970, 1, 1, 1, 0, 0, 0), 3600),
                                                  ((2016, 1, 1, 0, 0, 0, 0), 1451606400)] {
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

    #[test]
    fn test_format() {
        let paris = Timezone::new("Europe/Paris").unwrap();
        let t = paris.datetime(2006, 1, 2, 15, 4, 5, 123_456_789);

        assert_eq!(t.format("%Y-%m-%dT%H:%M:%S"), "2006-01-02T15:04:05");
        assert_eq!(t.format("%3"), "123");
        assert_eq!(t.format("%6"), "123456");
        assert_eq!(t.format("%9"), "123456789");
        assert_eq!(t.format("%z"), "+0100");
        assert_eq!(t.format("%Z"), "CET");
        assert_eq!(t.format("%w"), "1");
        assert_eq!(t.format("%a"), "Mon");
        assert_eq!(t.format("%A"), "Monday");
        assert_eq!(t.format("%b"), "Jan");
        assert_eq!(t.format("%B"), "January");
        assert_eq!(t.format("%C"), "20");
        assert_eq!(t.rfc3339(), "2006-01-02T15:04:05+01:00");
        assert_eq!(t.rfc2822(), "Mon, 2 Jan 2006 15:04:05 +0100");
    }
}

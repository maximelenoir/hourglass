//! `tzdata` uses the IANA Time Zone Database to provide conversion between timezones.
extern crate time;

mod parse;

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
    /// The extra transition rule
    trule: Option<TransRule>,
}

#[derive(Debug)]
struct Transition {
    utc: i64,
    ttype: Rc<Type>,
}

#[derive(Debug)]
enum TransRule {
    Fixed(Type),
    Alternate {
        dst_start: GenericDay,
        dst_stime: i32,
        dst_end: GenericDay,
        dst_etime: i32,
        std: Type,
        dst: Type,
    },
}

#[derive(Debug)]
enum GenericDay {
    Julian0 {
        jday: i32,
    },
    Julian1 {
        jday: i32,
    },
    MWDRule {
        month: i32,
        week: i32,
        wday: i32,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
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
            trule: None,
        }
    }

    /// Compute the UTC offset in this `Timezone` for unix timestamp `t`.
    fn offset(&self, stamp: i64) -> &Type {
        let idx = match self.trans.binary_search_by(|t| t.utc.cmp(&stamp)) {
            Err(i) if i == self.trans.len() => return self.offset_trule(stamp),
            Err(0) => 0,
            Err(i) => i - 1,
            Ok(i) => i,
        };

        &self.trans[idx].ttype
    }

    /// Compute the UTC offset in this `Timezone` for unix timestamp `t`
    /// using the transition rule.
    fn offset_trule(&self, stamp: i64) -> &Type {
        match self.trule {
            None => &self.trans.last().unwrap().ttype,
            Some(ref rule) => rule.get_type(stamp),
        }
    }

    /// Return the `Datetime` representing now, relative to this `Timezone`.
    pub fn now(&self) -> Datetime {
        Datetime {
            tz: self,
            stamp: time::get_time(),
            is_60th_sec: false,
        }
    }

    /// Parse a `Datetime` relative to this `Timezone` according
    /// to the given format. Timezone-related field are ignored.
    /// Panics if the string does not match the format.
    pub fn parse(&self, s: &str, fmt: &str) -> Datetime {
        let tm = time::strptime(s, fmt).unwrap();
        self.datetime(tm.tm_year + 1900,
                      tm.tm_mon + 1,
                      tm.tm_mday,
                      tm.tm_hour,
                      tm.tm_min,
                      tm.tm_sec,
                      tm.tm_nsec)
    }

    /// Create a new `Datetime` relative to this `Timezone`.
    /// Panics if the following constraints do not hold:
    ///
    /// - `month` ∊ [1, 12]
    /// - `day` ∊ [1, 31] and is valid within the month
    /// - `hour` ∊ [0, 23]
    /// - `minute` ∊ [0, 59]
    /// - `second` ∊ [0, 60]
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
        assert!(second <= 60);
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
            tm_sec: if second == 60 {
                59
            } else {
                second as i32
            },
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
            is_60th_sec: if second == 60 && year >= 1972 {
                if let Ok(_) = LEAP_SECONDS.binary_search(&stamp.sec) {
                    true
                } else {
                    panic!("not a valid leap second");
                }
            } else {
                false
            },
        }
    }
}

impl GenericDay {
    fn cmp_t(&self, tm: &time::Tm) -> Ordering {
        const DAYS_MONTH: &'static [i32] = &[0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

        let is_leap_year = (tm.tm_year % 4 == 0 && tm.tm_year % 100 != 0) || tm.tm_year % 400 == 0;

        match *self {
            GenericDay::Julian0 { jday } => jday.cmp(&tm.tm_yday),
            GenericDay::Julian1 { jday } => {
                let yday = if is_leap_year && tm.tm_mon > 2 {
                    tm.tm_yday
                } else {
                    tm.tm_yday + 1
                };
                jday.cmp(&yday)
            }
            GenericDay::MWDRule { month, week, wday } => {
                if month < tm.tm_mon {
                    Ordering::Less
                } else if month > tm.tm_mon {
                    Ordering::Greater
                } else {
                    let wday_on_first = (tm.tm_wday - tm.tm_mday + 1 + 5 * 7) % 7;
                    let days_in_month = if is_leap_year && tm.tm_mon == 2 {
                        29
                    } else {
                        DAYS_MONTH[tm.tm_mon as usize]
                    };

                    let mut matching_week = 0;
                    let mut last_matching_day = 0;
                    for d in 0..days_in_month {
                        if (wday_on_first + d) % 7 == wday {
                            last_matching_day = d;
                            matching_week += 1;
                        }
                        if matching_week == week {
                            break;
                        }
                    }
                    (last_matching_day + 1).cmp(&tm.tm_mday)
                }
            }
        }
    }

    fn approx_month(&self) -> i32 {
        match *self {
            GenericDay::Julian0 { jday } => jday / 30,
            GenericDay::Julian1 { jday } => jday / 30,
            GenericDay::MWDRule { month, .. } => month,
        }
    }

    fn cmp(&self, other: &GenericDay) -> Ordering {
        // I make the assumption that the dst
        // start and end are more than 1 month apart.
        self.approx_month().cmp(&other.approx_month())
    }
}

impl PartialEq<time::Tm> for GenericDay {
    fn eq(&self, tm: &time::Tm) -> bool {
        self.cmp_t(tm) == Ordering::Equal
    }
}

impl PartialOrd<time::Tm> for GenericDay {
    fn partial_cmp(&self, tm: &time::Tm) -> Option<Ordering> {
        Some(self.cmp_t(tm))
    }
}

impl PartialEq<GenericDay> for GenericDay {
    fn eq(&self, other: &GenericDay) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd<GenericDay> for GenericDay {
    fn partial_cmp(&self, other: &GenericDay) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl TransRule {
    fn get_type(&self, stamp: i64) -> &Type {
        match *self {
            TransRule::Fixed(ref t) => t,
            TransRule::Alternate { ref dst_start, dst_stime, ref dst_end, dst_etime, ref std, ref dst } => {
                let mut std_t = time::at_utc(time::Timespec { sec: stamp + std.off as i64, nsec: 0 });
                std_t.tm_year += 1900;
                std_t.tm_mon += 1;
                let std_sec = std_t.tm_hour * 3600 + std_t.tm_min * 60 + std_t.tm_sec;

                // TODO: more efficient way to compute dst_t from std_t?
                let mut dst_t = time::at_utc(time::Timespec { sec: stamp + dst.off as i64, nsec: 0 });
                dst_t.tm_year += 1900;
                dst_t.tm_mon += 1;
                let dst_sec = dst_t.tm_hour * 3600 + dst_t.tm_min * 60 + dst_t.tm_sec;

                if dst_start < dst_end {
                    match (dst_start.cmp_t(&std_t), dst_stime.cmp(&std_sec)) {
                        (Ordering::Greater, _) => std,
                        (Ordering::Equal, Ordering::Greater) => std,
                        (Ordering::Equal, _) => dst,
                        (_, _) => match (dst_end.cmp_t(&dst_t), dst_etime.cmp(&dst_sec)) {
                            (Ordering::Greater, _) => dst,
                            (Ordering::Equal, Ordering::Greater) => dst,
                            (Ordering::Equal, _) => std,
                            (_, _) => std,
                        },
                    }
                } else {
                    match (dst_end.cmp_t(&dst_t), dst_etime.cmp(&dst_sec)) {
                        (Ordering::Greater, _) => dst,
                        (Ordering::Equal, Ordering::Greater) => dst,
                        (Ordering::Equal, _) => std,
                        (_, _) => match (dst_start.cmp_t(&std_t), dst_stime.cmp(&std_sec)) {
                            (Ordering::Greater, _) => std,
                            (Ordering::Equal, Ordering::Greater) => std,
                            (Ordering::Equal, _) => dst,
                            (_, _) => dst,
                        }
                    }
                }
            }
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
    fn tm_to_time(tm: &time::Tm, is_60th_sec: bool) -> (i32, i32, i32, i32) {
        (tm.tm_hour,
         tm.tm_min,
         tm.tm_sec +
         if is_60th_sec {
            1
        } else {
            0
        },
         tm.tm_nsec)
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
        Self::tm_to_time(&tm, self.is_60th_sec)
    }

    /// Return the unix timestamp. This is the number of unix seconds
    /// since 1970-01-01T00:00:00Z.
    pub fn unix(&self) -> i64 {
        self.stamp.sec
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
        let time = Self::tm_to_time(&tm, self.is_60th_sec);
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
        self.cmp(&other) == Ordering::Equal
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

// FIXME: is reading /usr/share/zoneinfo/leap-seconds.list
// a better way to store the leap information?
const NTP_TO_UNIX: i64 = 2208988801;
const LEAP_SECONDS: &'static [i64] = &[2272060800 - NTP_TO_UNIX,
                                       2287785600 - NTP_TO_UNIX,
                                       2303683200 - NTP_TO_UNIX,
                                       2335219200 - NTP_TO_UNIX,
                                       2366755200 - NTP_TO_UNIX,
                                       2398291200 - NTP_TO_UNIX,
                                       2429913600 - NTP_TO_UNIX,
                                       2461449600 - NTP_TO_UNIX,
                                       2492985600 - NTP_TO_UNIX,
                                       2524521600 - NTP_TO_UNIX,
                                       2571782400 - NTP_TO_UNIX,
                                       2603318400 - NTP_TO_UNIX,
                                       2634854400 - NTP_TO_UNIX,
                                       2698012800 - NTP_TO_UNIX,
                                       2776982400 - NTP_TO_UNIX,
                                       2840140800 - NTP_TO_UNIX,
                                       2871676800 - NTP_TO_UNIX,
                                       2918937600 - NTP_TO_UNIX,
                                       2950473600 - NTP_TO_UNIX,
                                       2982009600 - NTP_TO_UNIX,
                                       3029443200 - NTP_TO_UNIX,
                                       3076704000 - NTP_TO_UNIX,
                                       3124137600 - NTP_TO_UNIX,
                                       3345062400 - NTP_TO_UNIX,
                                       3439756800 - NTP_TO_UNIX,
                                       3550089600 - NTP_TO_UNIX,
                                       3644697600 - NTP_TO_UNIX];

#[cfg(test)]
mod test {
    use super::*;
    use super::time;
    use super::{GenericDay, Type, TransRule};

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
    fn test_leap_second() {
        let utc = Timezone::utc();
        let t = utc.datetime(2015, 6, 30, 23, 59, 59, 0);
        let t_leap = utc.datetime(2015, 6, 30, 23, 59, 60, 0);
        assert_eq!(t.is_60th_sec, false);
        assert_eq!(t_leap.is_60th_sec, true);
        assert_eq!(t.stamp.sec, t_leap.stamp.sec);
        assert_eq!(t_leap.format("%S"), "60");
        assert_eq!(t_leap.time().2, 60);
        assert!(t_leap != t);
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

    #[test]
    fn test_parse() {
        let paris = Timezone::new("Europe/Paris").unwrap();
        let utc = Timezone::utc();

        let t = paris.parse("2006-01-02T15:04:05", "%Y-%m-%dT%H:%M:%S");
        let t_utc = t.project(&utc);
        assert_eq!(t_utc.date(), (2006, 1, 2));
        assert_eq!(t_utc.time(), (14, 4, 5, 0));
    }

    #[test]
    fn test_generic_day() {
        fn t(y: i32, m: i32, d: i32) -> time::Tm {
            let tm = time::Tm {
                tm_sec: 0,
                tm_min: 0,
                tm_hour: 0,
                tm_mday: d,
                tm_mon: m - 1,
                tm_year: y - 1900,
                tm_wday: 0,
                tm_yday: 0,
                tm_isdst: 0,
                tm_utcoff: 0,
                tm_nsec: 0,
            };
            // Trick to let time lib compute tm_wday.
            let t = tm.to_timespec();
            let mut tm = time::at_utc(t);
            tm.tm_year += 1900;
            tm.tm_mon += 1;
            tm
        }

        assert_eq!(GenericDay::Julian1 { jday: 59 }, t(2016, 2, 28));
        assert_eq!(GenericDay::Julian1 { jday: 60 }, t(2016, 3, 1));
        assert_eq!(GenericDay::Julian1 { jday: 365 }, t(2016, 12, 31));
        assert_eq!(GenericDay::Julian1 { jday: 59 }, t(2015, 2, 28));
        assert_eq!(GenericDay::Julian1 { jday: 60 }, t(2015, 3, 1));
        assert_eq!(GenericDay::Julian1 { jday: 365 }, t(2015, 12, 31));

        assert_eq!(GenericDay::Julian0 { jday: 58 }, t(2016, 2, 28));
        assert_eq!(GenericDay::Julian0 { jday: 59 }, t(2016, 2, 29));
        assert_eq!(GenericDay::Julian0 { jday: 60 }, t(2016, 3, 1));
        assert_eq!(GenericDay::Julian0 { jday: 365 }, t(2016, 12, 31));
        assert_eq!(GenericDay::Julian0 { jday: 58 }, t(2015, 2, 28));
        assert_eq!(GenericDay::Julian0 { jday: 59 }, t(2015, 3, 1));
        assert_eq!(GenericDay::Julian0 { jday: 364 }, t(2015, 12, 31));

        assert_eq!(GenericDay::MWDRule {
                       month: 1,
                       week: 1,
                       wday: 0,
                   },
                   t(2016, 1, 3));
        assert_eq!(GenericDay::MWDRule {
                       month: 1,
                       week: 2,
                       wday: 0,
                   },
                   t(2016, 1, 10));
        assert_eq!(GenericDay::MWDRule {
                       month: 1,
                       week: 5,
                       wday: 0,
                   },
                   t(2016, 1, 31));
        assert_eq!(GenericDay::MWDRule {
                       month: 1,
                       week: 1,
                       wday: 5,
                   },
                   t(2016, 1, 1));
        assert_eq!(GenericDay::MWDRule {
                       month: 1,
                       week: 5,
                       wday: 4,
                   },
                   t(2016, 1, 28));
        assert_eq!(GenericDay::MWDRule {
                       month: 1,
                       week: 4,
                       wday: 4,
                   },
                   t(2016, 1, 28));
    }

    #[test]
    fn test_trans_rule() {
        fn s(y: i32, mo: i32, d: i32, h: i32, m: i32, s: i32) -> i64 {
            let tm = time::Tm {
                tm_sec: s,
                tm_min: m,
                tm_hour: h,
                tm_mday: d,
                tm_mon: mo - 1,
                tm_year: y - 1900,
                tm_wday: 0,
                tm_yday: 0,
                tm_isdst: 0,
                tm_utcoff: 0,
                tm_nsec: 0,
            };
            tm.to_timespec().sec
        }

        // Fixed offset rule. easy.
        let kst = Type {
            off: 9 * 3600,
            is_dst: false,
            abbr: "KST".to_owned(),
        };
        let seoul_rule = TransRule::Fixed(kst.clone());
        assert_eq!(seoul_rule.get_type(s(2016, 1, 1, 0, 0, 0)), &kst);
        assert_eq!(seoul_rule.get_type(s(2016, 7, 1, 0, 0, 0)), &kst);
        assert_eq!(seoul_rule.get_type(s(2016, 10, 1, 0, 0, 0)), &kst);

        // Alternate offset rule.
        // CET-1CEST,M3.5.0,M10.5.0/3
        let cet = Type {
            off: 1 * 3600,
            is_dst: false,
            abbr: "CET".to_owned(),
        };
        let cest = Type {
            off: 2 * 3600,
            is_dst: true,
            abbr: "CEST".to_owned(),
        };
        let paris_rule = TransRule::Alternate {
            dst_start: GenericDay::MWDRule {
                month: 3,
                week: 5,
                wday: 0,
            },
            dst_stime: 2 * 3600, // From std to dst at 2AM std tz
            dst_end: GenericDay::MWDRule {
                month: 10,
                week: 5,
                wday: 0,
            },
            dst_etime: 3 * 3600, // From dst to std at 3AM dst tz!
            std: cet.clone(),
            dst: cest.clone(),
        };
        assert_eq!(paris_rule.get_type(s(2016, 1, 1, 0, 0, 0)), &cet);
        assert_eq!(paris_rule.get_type(s(2016, 3, 27, 0, 59, 59)), &cet);
        assert_eq!(paris_rule.get_type(s(2016, 3, 27, 1, 0, 0)), &cest);
        assert_eq!(paris_rule.get_type(s(2016, 10, 30, 0, 59, 59)), &cest);
        assert_eq!(paris_rule.get_type(s(2016, 10, 30, 1, 0, 0)), &cet);
        assert_eq!(paris_rule.get_type(s(2016, 12, 31, 0, 0, 0)), &cet);

        // Alternate offset rule where dst is still
        // in use at the end of the year and stops at
        // the beginning of the year.
        // AEST-10AEDT,M10.1.0,M4.1.0/3
        let aest = Type {
            off: 10 * 3600,
            is_dst: false,
            abbr: "AEST".to_owned(),
        };
        let aedt = Type {
            off: 11 * 3600,
            is_dst: true,
            abbr: "AEDT".to_owned(),
        };
        let sydney_rule = TransRule::Alternate {
            dst_start: GenericDay::MWDRule {
                month: 10,
                week: 1,
                wday: 0,
            },
            dst_stime: 2 * 3600,
            dst_end: GenericDay::MWDRule {
                month: 4,
                week: 1,
                wday: 0,
            },
            dst_etime: 3 * 3600,
            std: aest.clone(),
            dst: aedt.clone(),
        };
        assert_eq!(sydney_rule.get_type(s(2016, 1, 1, 0, 0, 0)), &aedt);
        assert_eq!(sydney_rule.get_type(s(2016, 4, 2, 15, 59, 59)), &aedt);
        assert_eq!(sydney_rule.get_type(s(2016, 4, 2, 16, 0, 0)), &aest);
        assert_eq!(sydney_rule.get_type(s(2016, 10, 1, 15, 59, 59)), &aest);
        assert_eq!(sydney_rule.get_type(s(2016, 10, 1, 16, 0, 0)), &aedt);
        assert_eq!(sydney_rule.get_type(s(2016, 12, 31, 0, 0, 0)), &aedt);

        // Alternative offset with negative UTC offset
        // EST5EDT,M3.2.0,M11.1.0
        let est = Type {
            off: -5 * 3600,
            is_dst: false,
            abbr: "EST".to_owned(),
        };
        let edt = Type {
            off: -4 * 3600,
            is_dst: true,
            abbr: "EDT".to_owned(),
        };
        let newyork_rule = TransRule::Alternate {
            dst_start: GenericDay::MWDRule {
                month: 3,
                week: 2,
                wday: 0,
            },
            dst_stime: 2 * 3600,
            dst_end: GenericDay::MWDRule {
                month: 11,
                week: 1,
                wday: 0,
            },
            dst_etime: 2 * 3600,
            std: est.clone(),
            dst: edt.clone(),
        };
        assert_eq!(newyork_rule.get_type(s(2016, 1, 1, 0, 0, 0)), &est);
        assert_eq!(newyork_rule.get_type(s(2016, 3, 13, 6, 59, 59)), &est);
        assert_eq!(newyork_rule.get_type(s(2016, 3, 13, 7, 0, 0)), &edt);
        assert_eq!(newyork_rule.get_type(s(2016, 11, 6, 5, 59, 59)), &edt);
        assert_eq!(newyork_rule.get_type(s(2016, 11, 6, 6, 0, 0)), &est);
        assert_eq!(newyork_rule.get_type(s(2016, 12, 31, 0, 0, 0)), &est);
    }
}

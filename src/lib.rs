//! `hourglass` provides support for timezone, datetime arithmetic and take care
//! of subtleties related to time handling, like leap seconds.
//!
//! ## Usage
//!
//! Add the following in your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! hourglass = "0.*"
//! ```
//!
//! And put this in your crate root:
//!
//! ```rust
//! extern crate hourglass;
//! ```
//!
//! ## Overview
//!
//! ### Timezone
//!
//! Because a datetime without a timezone is ambiguous and error-prone, `hourglass`
//! only exposes a `Datetime` that is timezone-aware. The creation of a `Timezone`
//! is the entry point of the API. `hourglass` provides several way of creating
//! a `Timezone`:
//!
//! ```rust
//! use hourglass::Timezone;
//!
//! let utc = Timezone::utc();
//! let local = Timezone::local().unwrap();
//! let paris = Timezone::new("Europe/Paris").unwrap();
//! let fixed = Timezone::fixed(-5 * 3600);
//! ```
//!
//! A `Datetime` is created for a specific timezone and can be projected in another
//! timezone:
//!
//! ```rust
//! use hourglass::Timezone;
//!
//! let utc = Timezone::utc();
//! let paris = Timezone::new("Europe/Paris").unwrap();
//!
//! // Create a `Datetime` corresponding to midnight in Paris timezone...
//! let t = paris.datetime(2015, 12, 25, 0, 0, 0, 0).unwrap();
//! // ... and project it into UTC timezone.
//! let t_utc = t.project(&utc);
//! assert_eq!(t_utc.date(), (2015, 12, 24));
//! assert_eq!(t_utc.time(), (23, 0, 0, 0));
//! ```
//!
//! ### Arithmetic
//!
//! `Datetime` arithmetic is performed with a `Deltatime`. Several granularities
//! are available when handling `Deltatime` and will yield different results:
//!
//! ```rust
//! use hourglass::{Timezone, Deltatime};
//!
//! let utc = Timezone::utc();
//! let t = utc.datetime(2015, 6, 30, 0, 0, 0, 0).unwrap();
//! let t_plus_1_day = t + Deltatime::days(1);
//! let t_plus_86400_sec = t + Deltatime::seconds(86400);
//!
//! assert_eq!(t_plus_1_day.date(), (2015, 7, 1));
//! // One leap second was inserted this day.
//! assert_eq!(t_plus_86400_sec.date(), (2015, 6, 30));
//! assert_eq!(t_plus_86400_sec.time(), (23, 59, 60, 0));
//! ```
//!
//! Two `Datetime` can also be compared:
//!
//! ```rust
//! use hourglass::{Timezone, Deltatime};
//!
//! let utc = Timezone::utc();
//! let t0 = utc.datetime(2015, 6, 30, 0, 0, 0, 0).unwrap();
//! let t1 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();
//!
//! assert_eq!(t0 < t1, true);
//! assert_eq!(t0 >= t1, false);
//! assert_eq!(t1 == t1, true);
//! assert_eq!(t1 - t0, Deltatime::seconds(86401));
//! ```
//!
//! ### Iterators
//!
//! `hourglass` also provides the `Every` iterator for scheduling a loop
//! body execution at regular time interval:
//!
//! ```rust
//! use hourglass::{Timezone, Deltatime, Timespec, Every};
//!
//! let paris = Timezone::new("Europe/Paris").unwrap();
//! let until = Timespec::now() + Deltatime::seconds(5);
//!
//! for t in Every::until(Deltatime::seconds(1), until) {
//!     println!("it is {} in Paris", t.to_datetime(&paris).format("%H:%M:%S").unwrap());
//! }
//! ```
//!
//! The `Range` iterator can be used to iterate over a range of `Timespec`:
//!
//! ```rust
//! use hourglass::{Deltatime, Timespec, Range};
//!
//! let now = Timespec::now();
//! let then = now + Deltatime::minutes(1);
//!
//! for t in Range::new(now, then, Deltatime::seconds(1)) {
//!     println!("tick {}", t.seconds());
//! }
//! ```

#[macro_use]
extern crate nom;
extern crate libc;

mod parse;
mod iter;
mod sys;

pub use iter::{Every, Range};

use std::rc::Rc;
use std::io;
use std::fmt;
use std::ptr;
use std::error;
use std::cmp::{Eq, PartialEq, Ord, PartialOrd, Ordering};
use std::ops::{Add, Sub, Neg};
use std::str::FromStr;
use nom::{digit, alpha, eof, IResult};

/// A timezone.
///
/// There are several ways to create a new `Timezone`. It can be loaded from the
/// [`IANA Time Zone Database`](https://www.iana.org/time-zones), following the `Area/Location`
/// pattern (e.g. `Europe/Paris`) with `Timezone::new`. A `Timezone` can be created as a fixed offset from `UTC`
/// with `Timezone::fixed` or `UTC` itself with `Timezone::utc`. Finally, the `Timezone` can match the
/// system local timezone with `Timezone::local`.
///
/// # Example
///
/// ```rust
/// let utc = hourglass::Timezone::utc();
/// let now = utc.now();
///
/// for tzname in &["Europe/Paris", "America/New_York", "Asia/Seoul"] {
///     let tz = hourglass::Timezone::new(tzname).unwrap();
///     let now = now.project(&tz);
///     println!("it is now {:?} in {}", now, tzname);
/// }
/// ```
pub struct Timezone {
    /// The `UTC` offset transitions
    trans: Vec<Transition>,
    /// The extra transition rule
    trule: Option<TransRule>,
}

#[derive(Debug)]
struct Transition {
    utc: i64,
    ttype: Rc<Type>,
}

#[derive(Debug, Eq, PartialEq)]
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

#[derive(Debug, Eq, PartialEq)]
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
    pub fn new(timezone: &str) -> Result<Self, TzError> {
        parse::load_timezone(timezone)
    }

    /// Load the local `Timezone` set by the system,
    /// disregarding the `TZ` environment variable.
    pub fn local() -> Result<Self, TzError> {
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

    /// Create a `Timezone` from a POSIX TZ definition.
    /// See `man 3 tzset` for a description of the format.
    pub fn posix(posix: &str) -> Result<Self, TzError> {
        match posixtz(posix) {
            IResult::Done(_, rule) => {
                Ok(Timezone {
                    trans: vec![],
                    trule: Some(rule),
                })
            }
            _ => Err(TzError::InvalidPosixTz),
        }
    }

    /// Compute the `UTC` offset in this `Timezone` for unix timestamp `t`.
    fn offset(&self, stamp: i64) -> &Type {
        let idx = match self.trans.binary_search_by(|t| t.utc.cmp(&stamp)) {
            Err(i) if i == self.trans.len() => return self.offset_trule(stamp),
            Err(0) => 0,
            Err(i) => i - 1,
            Ok(i) => i,
        };

        &self.trans[idx].ttype
    }

    /// Compute the `UTC` offset in this `Timezone` for unix timestamp `t`
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
            stamp: Timespec::now(),
        }
    }

    /// Parse a `Datetime` relative to this `Timezone` according to the
    /// given format. Timezone-related field are ignored. An `InputError`
    /// is returned if the string does not match the format.
    pub fn parse(&self, s: &str, fmt: &str) -> Result<Datetime, InputError> {
        let mut tm = libc::tm {
            tm_sec: 0,
            tm_min: 0,
            tm_hour: 0,
            tm_mday: 1,
            tm_mon: 0,
            tm_year: 0,
            tm_wday: 0,
            tm_yday: 0,
            tm_isdst: 0,
            // Unused
            tm_gmtoff: 0,
            tm_zone: sys::empty_tm_zone(),
        };

        // We have to handle ending \x00 byte.
        let s = try!(std::ffi::CString::new(s).map_err(|_| InputError::InvalidFormat));
        let fmt = try!(std::ffi::CString::new(fmt).map_err(|_| InputError::InvalidFormat));

        let ret = unsafe {
            strptime(s.as_ptr() as *const libc::c_char,
                     fmt.as_ptr() as *const libc::c_char,
                     &mut tm)
        };

        if ret == ptr::null() {
            Err(InputError::InvalidFormat)
        } else {
            self.datetime(tm.tm_year + 1900,
                          tm.tm_mon + 1,
                          tm.tm_mday,
                          tm.tm_hour,
                          tm.tm_min,
                          tm.tm_sec,
                          0)
        }
    }

    /// Create a new `Datetime` from a Unix timestamp. The provided
    /// timestamp represents Unix seconds from the Epoch, discarding any
    /// leap seconds that may have happened in between. A Unix timestamp
    /// is ambiguous on leap second insertion (e.g. `1435708800` is
    /// equal to both `2015-06-30T23:59:60Z` and `2015-07-01T00:00:00Z`)
    /// however, `unix` will always choose the non-leap second. Return
    /// an `InputError` if `nano` ∉ [0, 999999999].
    pub fn unix(&self, stamp: i64, nano: i32) -> Result<Datetime, InputError> {
        Ok(Datetime {
            tz: self,
            stamp: try!(Timespec::unix(stamp, nano)),
        })
    }

    /// Create a new `Datetime` relative to this `Timezone`.
    /// An `InputError` is returned if the following constraints do not hold:
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
                    -> Result<Datetime, InputError> {
        let is_leap_year = (year % 4 == 0 && year % 100 != 0) || year % 400 == 0;

        // Error if constaints described in documentation do not hold.
        if month < 1 || month > 12 {
            return Err(InputError::InvalidMonth);
        } else if hour < 0 || hour > 23 {
            return Err(InputError::InvalidHour);
        } else if minute < 0 || minute > 59 {
            return Err(InputError::InvalidMinute);
        } else if second < 0 || second > 60 {
            return Err(InputError::InvalidSecond);
        } else if nano < 0 || nano > 999_999_999 {
            return Err(InputError::InvalidNano);
        }

        let max_day = match month {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
            4 | 6 | 9 | 11 => 30,
            2 if is_leap_year => 30,
            2 => 29,
            _ => unreachable!(),
        };

        if day < 1 || day > max_day {
            return Err(InputError::InvalidDay);
        }

        // Let the libc do the heavy lifting.
        let utc_dt = libc::tm {
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
            tm_gmtoff: 0,
            tm_zone: sys::empty_tm_zone(),
        };

        let mut sec = tm_to_stamp(&utc_dt);
        let utc_offset = self.offset(sec).off;
        sec -= utc_offset as i64;

        if second == 60 {
            if let Err(_) = LEAP_SECONDS.binary_search(&(sec + 1)) {
                return Err(InputError::InvalidLeapSecond);
            }
            Ok(Datetime {
                tz: self,
                // The stamp actually corresponds to 00:00:00. I cheated
                // when making tm_to_stamp compute the stamp (I used
                // 59 instead of 60 seconds) because of the lack of
                // leap second support in unix timestamp. We need to
                // adjust now.
                stamp: Timespec {
                    sec: sec + 1,
                    nano: nano,
                    leaping: true,
                },
            })
        } else {
            Ok(Datetime {
                tz: self,
                stamp: Timespec {
                    sec: sec,
                    nano: nano,
                    leaping: false,
                },
            })
        }
    }
}

// Match an ascii number and convert it to an i32.
named!(num<&str, i32>, map_res!(digit, FromStr::from_str));

// Match "hh[:mm[:ss]]" and returns the number of seconds.
named!(hhmmss<&str, i32>,
    chain!(
        hour: num ~
        sec: opt!(complete!(chain!(
            tag_s!(":") ~
            min: num ~
            sec: opt!(complete!(chain!(
                tag_s!(":") ~
                sec: num,
                || { sec }
            ))),
            || { min * 60 + sec.unwrap_or(0) }
        ))),
        || { hour * 3600 + sec.unwrap_or(0) }
    )
);

// Match "[+-]hh[:mm[:ss]]" and returns the number of seconds.
named!(signed_hhmmss<&str, i32>, chain!(
    sign: chain!(
        s: alt!(tag_s!("+") | tag_s!("-"))?,
        || { if let Some("-") = s { -1 } else { 1 } }
    ) ~
    sec: hhmmss,
    || { sign * sec }
));


// Match a generic day definition "Jn", "n" or "Mm.w.d".
named!(genday<&str, GenericDay>,
    alt!(
        chain!(
            tag_s!("J") ~
            j: num,
            || { GenericDay::Julian1 { jday: j } }
        ) |
        chain!(
            tag_s!("M") ~
            m: num ~
            tag_s!(".") ~
            w: num ~
            tag_s!(".") ~
            d: num,
            || { GenericDay::MWDRule { month: m, week: w, wday: d } }
        ) |
        num => { |j| { GenericDay::Julian0 { jday: j } } }
    )
);

// Match a POSIX TZ definition "std offset[dst[offset][,start[/time],end[/time]]]"
named!(posixtz<&str, TransRule>, alt!(
    chain!(
        std_abbr: alpha ~
        std_off: signed_hhmmss ~
        eof,
        || {
            TransRule::Fixed(
                Type{
                    off: -std_off,
                    is_dst: false,
                    abbr: std_abbr.to_owned(),
                }
            )
        }
    ) |
    chain!(
        std_abbr: alpha ~
        std_off: signed_hhmmss ~
        dst_abbr: alpha ~
        dst_off: opt!(complete!(signed_hhmmss)) ~
        tag_s!(",") ~
        dst_start: genday ~
        dst_stime: opt!(complete!(preceded!(tag_s!("/"), hhmmss))) ~
        tag_s!(",") ~
        dst_end: genday ~
        dst_etime: opt!(complete!(preceded!(tag_s!("/"), hhmmss))) ~
        eof,
        || {
            TransRule::Alternate {
                dst_start: dst_start,
                dst_stime: dst_stime.unwrap_or(2 * 3600),
                dst_end: dst_end,
                dst_etime: dst_etime.unwrap_or(2 * 3600),
                std: Type {
                    off: -std_off,
                    is_dst: false,
                    abbr: std_abbr.to_owned(),
                },
                dst: Type {
                    off: -dst_off.unwrap_or(std_off - 3600),
                    is_dst: true,
                    abbr: dst_abbr.to_owned(),
                },
            }
        }
    )
));


impl GenericDay {
    fn cmp_t(&self, tm: &libc::tm) -> Ordering {
        const DAYS_MONTH: &'static [i32] = &[0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
        let tm_year = tm.tm_year + 1900;
        let tm_mon = tm.tm_mon + 1;

        let is_leap_year = (tm_year % 4 == 0 && tm_year % 100 != 0) || tm_year % 400 == 0;

        match *self {
            GenericDay::Julian0 { jday } => jday.cmp(&tm.tm_yday),
            GenericDay::Julian1 { jday } => {
                let yday = if is_leap_year && tm_mon > 2 {
                    tm.tm_yday
                } else {
                    tm.tm_yday + 1
                };
                jday.cmp(&yday)
            }
            GenericDay::MWDRule { month, week, wday } => {
                if month < tm_mon {
                    Ordering::Less
                } else if month > tm_mon {
                    Ordering::Greater
                } else {
                    let wday_on_first = (tm.tm_wday - tm.tm_mday + 1 + 5 * 7) % 7;
                    let days_in_month = if is_leap_year && tm_mon == 2 {
                        29
                    } else {
                        DAYS_MONTH[tm_mon as usize]
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

impl PartialEq<libc::tm> for GenericDay {
    fn eq(&self, tm: &libc::tm) -> bool {
        self.cmp_t(tm) == Ordering::Equal
    }
}

impl PartialOrd<libc::tm> for GenericDay {
    fn partial_cmp(&self, tm: &libc::tm) -> Option<Ordering> {
        Some(self.cmp_t(tm))
    }
}

impl TransRule {
    fn get_type(&self, stamp: i64) -> &Type {
        match *self {
            TransRule::Fixed(ref t) => t,
            TransRule::Alternate { ref dst_start, dst_stime, ref dst_end, dst_etime, ref std, ref dst } => {
                let std_t = stamp_to_tm(stamp + std.off as i64);
                let std_sec = std_t.tm_hour * 3600 + std_t.tm_min * 60 + std_t.tm_sec;

                // TODO: more efficient way to compute dst_t from std_t?
                let dst_t = stamp_to_tm(stamp + dst.off as i64);
                let dst_sec = dst_t.tm_hour * 3600 + dst_t.tm_min * 60 + dst_t.tm_sec;

                if dst_start.cmp(&dst_end) == Ordering::Less {
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

/// An offset from the Unix Epoch.
///
/// `Timespec` is the building block of `Datetime` and can be converted
/// from and to a `Datetime`. It is intrinsically expressed in the `UTC`
/// timezone since it holds the number of seconds elapsed since the Unix
/// Epoch `1970-01-01T00:00:00Z` and therefore is not ambiguous.
///
/// It is equivalent to a `Datetime` without `Timezone` information and
/// therefore does not have access to as much methods as its counterpart.
/// For example, its `date` representation cannot be computed.  In return,
/// the type is simpler and easier to handle and move around. Like
/// `Datetime`, `Timespec` is leap second aware.
#[derive(Clone, Copy, Debug)]
pub struct Timespec {
    /// The offset since Unix Epoch. This is *not* the number
    /// of SI seconds since Unix Epoch because of leap seconds.
    sec: i64,
    /// The nanoseconds for the current second.
    nano: i32,
    /// Mark the leaping second.
    leaping: bool,
}

impl Timespec {
    /// Return the `Timespec` representing now.
    pub fn now() -> Timespec {

        let (tv_sec, tv_nsec) = sys::get_time();
        Timespec {
            sec: tv_sec,
            nano: tv_nsec as i32,
            leaping: false,
        }
    }

    /// Create a new `Timespec` from a Unix timestamp. An `InputError`
    /// is returned if `nano` ∉ [0, 999999999].
    pub fn unix(stamp: i64, nano: i32) -> Result<Timespec, InputError> {
        if nano < 0 || nano > 999_999_999 {
            return Err(InputError::InvalidNano);
        }

        Ok(Timespec {
            sec: stamp,
            nano: nano,
            leaping: false,
        })
    }

    /// Get the number of Unix seconds since the Unix Epoch.
    pub fn seconds(&self) -> i64 {
        self.sec
    }

    /// Get the number of nanoseconds elapsed for the current second.
    pub fn nanoseconds(&self) -> i32 {
        self.nano
    }

    /// Convert the `Timespec` into a `Datetime`, given a `Timezone`.
    /// Note the `Timespec` is always expressed as a Unix time, so
    /// converting to a `Datetime` won't interpret the `Timespec` as
    /// anything other than an offset from Unix Epoch in `UTC` timezone.
    pub fn to_datetime<'a>(&self, tz: &'a Timezone) -> Datetime<'a> {
        Datetime {
            tz: tz,
            stamp: *self,
        }
    }
}

impl PartialEq<Timespec> for Timespec {
    fn eq(&self, other: &Timespec) -> bool {
        self.cmp(&other) == Ordering::Equal
    }
}

impl Eq for Timespec {}

impl PartialOrd<Timespec> for Timespec {
    fn partial_cmp(&self, other: &Timespec) -> Option<Ordering> {
        let cmp_sec = self.sec.cmp(&other.sec);
        if let Ordering::Equal = cmp_sec {
            // Having the 60th sec tag means
            // that the time is Ordering::Less than
            // the other time.
            let cmp_leap = other.leaping.cmp(&self.leaping);
            if let Ordering::Equal = cmp_leap {
                Some(self.nano.cmp(&other.nano))
            } else {
                Some(cmp_leap)
            }
        } else {
            Some(cmp_sec)
        }
    }
}

impl Ord for Timespec {
    fn cmp(&self, other: &Timespec) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Add<Deltatime> for Timespec {
    type Output = Timespec;
    fn add(mut self, rhs: Deltatime) -> Self::Output {
        match rhs.0 {
            Delta::Nanoseconds(nano) => {
                if nano < 0 {
                    let nano = -nano;
                    if self.nano as i64 >= nano {
                        self.nano -= nano as i32;
                        return self;
                    }

                    let nano = nano - self.nano as i64;
                    let (sec, nano) = {
                        let s = nano / 1_000_000_000 + 1;
                        let n = s * 1_000_000_000 - nano;
                        if n == 1_000_000_000 {
                            (s - 1, 0)
                        } else {
                            (s, n)
                        }
                    };
                    let mut t = self + Deltatime(Delta::Seconds(-sec));
                    t.nano = nano as i32;
                    t
                } else {
                    let nano = nano + self.nano as i64;
                    if nano < 1_000_000_000 {
                        self.nano = nano as i32;
                        return self;
                    }

                    // Let's mentally empty the dt's nano counter. They will
                    // be added later. This trick is to avoid landing on a
                    // leap second when we add the remaining nano after the
                    // full seconds were added.
                    let sec = nano / 1_000_000_000;
                    let nano = nano - sec * 1_000_000_000;
                    let mut t = self + Deltatime(Delta::Seconds(sec));
                    t.nano = nano as i32;
                    t
                }
            }
            Delta::Seconds(mut sec) => {
                // TODO: version without loops ?
                if sec < 0 {
                    sec = -sec;
                    while sec != 0 {
                        match LEAP_SECONDS.binary_search(&self.sec) {
                            Err(0) => {
                                // We won't encounter any leap second.
                                self.sec -= sec;
                                return self;
                            }
                            Err(s) => {
                                let prev_leap = LEAP_SECONDS[s - 1];
                                let prev_leap_in_sec = self.sec - prev_leap;
                                if sec <= prev_leap_in_sec {
                                    // We're done before reaching the
                                    // previous leap second.
                                    self.sec -= sec;
                                    return self;
                                } else if sec == prev_leap_in_sec + 1 {
                                    // We've landed on the leap second.
                                    self.leaping = true;
                                    self.sec = prev_leap;
                                    return self;
                                } else {
                                    // We jump right before the leap second
                                    // while retaining 1 sec from the counter.
                                    self.sec = prev_leap - 1;
                                    sec -= prev_leap_in_sec + 2;
                                }
                            }
                            Ok(_) => {
                                // We start on an ambiguous unix timestamp.
                                if self.leaping {
                                    self.leaping = false;
                                    self.sec -= 1;
                                } else {
                                    self.leaping = true;
                                }
                                sec -= 1;
                            }
                        }
                    }
                    self
                } else {
                    while sec != 0 {
                        match LEAP_SECONDS.binary_search(&self.sec) {
                            Err(s) if s == LEAP_SECONDS.len() => {
                                // No leap seconds after current datetime.
                                // So we can safely add all the second and
                                // return the result.
                                self.sec += sec;
                                return self;
                            }
                            Err(s) => {
                                let next_leap = LEAP_SECONDS[s];
                                let next_leap_in_sec = next_leap - self.sec;
                                if sec < next_leap_in_sec {
                                    // We're done before even reaching the next
                                    // leap second.
                                    self.sec += sec;
                                    return self;
                                } else if sec == next_leap_in_sec {
                                    // We've landed on the leap second.
                                    self.sec = next_leap;
                                    self.leaping = true;
                                    return self;
                                } else {
                                    // Take into account the leap second
                                    // and countinue with whatever is left
                                    // of our second counter.
                                    self.sec = next_leap;
                                    sec -= next_leap_in_sec + 1;
                                }
                            }
                            Ok(_) => {
                                // We start on an ambiguous unix timestamp.
                                // If we know we're on leap second, just
                                // remove the leap marker and remove
                                // one second. Otherwise, just move one
                                // second. Either way, we just jump out of
                                // the ambiguous zone, without having our
                                // second counter < 0.
                                if self.leaping {
                                    self.leaping = false;
                                } else {
                                    self.sec += 1;
                                }
                                sec -= 1;
                            }
                        }
                    }
                    self
                }
            }
            Delta::Days(day) => {
                self.leaping = false;
                self.sec += day * 86400;
                self
            }
        }
    }
}

impl Sub<Deltatime> for Timespec {
    type Output = Timespec;
    fn sub(self, rhs: Deltatime) -> Self::Output {
        self + (-rhs)
    }
}

impl Sub<Timespec> for Timespec {
    type Output = Deltatime;
    fn sub(self, rhs: Timespec) -> Self::Output {
        if self < rhs {
            return -(rhs - self);
        }

        // rhs <= self
        let add_sec = match (LEAP_SECONDS.binary_search(&rhs.sec),
                             LEAP_SECONDS.binary_search(&self.sec)) {
            (Err(i), Err(j)) => (j - i) as i64,
            (Err(i), Ok(j)) => {
                (j - i) as i64 +
                if self.leaping {
                    0i64
                } else {
                    1i64
                }
            }
            (Ok(i), Err(j)) => {
                (j - i) as i64 +
                if rhs.leaping {
                    0i64
                } else {
                    -1i64
                }
            }
            (Ok(i), Ok(j)) => {
                (j - i) as i64 +
                if rhs.leaping {
                    0i64
                } else {
                    -1i64
                } +
                if self.leaping {
                    0i64
                } else {
                    1i64
                }
            }
        };
        Deltatime::nanoseconds((self.sec - rhs.sec + add_sec) * 1_000_000_000 +
                               (self.nano - rhs.nano) as i64)
    }
}

/// A precise point in time along associated to a `Timezone`.
///
/// The `Datetime` cannot be created on its own as it depends on
/// a `Timezone`. `hourglass` does not expose a naive flavor of Datetime.
/// To build a `Datetime`, instanciate a `Timezone` first and call
/// the desired method.
///
/// ```rust
/// let paris = hourglass::Timezone::new("Europe/Paris").unwrap();
/// let midnight_in_paris = paris.datetime(2015, 12, 25, 0, 0, 0, 0).unwrap();
///
/// let utc = hourglass::Timezone::utc();
/// let t = midnight_in_paris.project(&utc);
///
/// assert_eq!(t.date(), (2015, 12, 24));
/// assert_eq!(t.time(), (23, 0, 0, 0));
/// ```
#[derive(Clone, Copy)]
pub struct Datetime<'a> {
    /// The associated timezone.
    tz: &'a Timezone,
    /// The offset since Unix Epoch.
    stamp: Timespec,
}

impl<'a> Datetime<'a> {
    /// Project the current `Datetime` in another `Timezone`.
    pub fn project<'b>(&self, tz: &'b Timezone) -> Datetime<'b> {
        Datetime {
            tz: tz,
            stamp: self.stamp,
        }
    }

    /// Return the tm in the associated `Timezone`.
    fn tm(&self) -> libc::tm {
        let offset = self.tz.offset(self.stamp.sec).off;
        let mut tm = stamp_to_tm(self.stamp.sec + offset as i64 +
                                 if self.stamp.leaping {
            -1
        } else {
            0
        });
        if self.stamp.leaping {
            tm.tm_sec = 60;
        }
        tm
    }

    /// Convert a tm to date.
    fn tm_to_date(tm: &libc::tm) -> (i32, i32, i32) {
        (tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday)
    }

    /// Convert a tm to time.
    fn tm_to_time(tm: &libc::tm) -> (i32, i32, i32) {
        (tm.tm_hour, tm.tm_min, tm.tm_sec)
    }

    /// Convert a tm to weekday string.
    fn tm_to_weekday(tm: &libc::tm) -> &'static str {
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
    fn tm_to_month(tm: &libc::tm) -> &'static str {
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
        let (h, m, s) = Self::tm_to_time(&tm);
        (h, m, s, self.stamp.nano)
    }

    /// Return the unix timestamp. This is the number of unix seconds
    /// since `1970-01-01T00:00:00Z`.
    pub fn unix(&self) -> i64 {
        self.stamp.sec
    }

    /// Convert the `Datetime` to a `Timespec`, disregarding the
    /// `Timezone`. The associated `Timezone` does not have any impact on
    /// the resulting `Timespec`. Therefore, as long as two `Datetime`
    /// with different `Timezone` match the same point in time, their
    /// resulting `Timespec` will be equal.
    pub fn to_timespec(&self) -> Timespec {
        self.stamp
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
    /// - `%x`: `UTC` offset (+02:00 or -05:00)
    /// - `%z`: `UTC` offset (+0200 or -0500)
    /// - `%Z`: timezone abbreviation (CET)
    /// - `%w`: weekday (1)
    /// - `%a`: abbreviated weekday name (Mon)
    /// - `%A`: full weekday name (Monday)
    /// - `%b`: abbreviated month name (Jan)
    /// - `%B`: full month name (January)
    /// - `%C`: century (20)
    ///
    /// Returns a `FmtError` if the format is invalid.
    pub fn format(&self, fmt: &str) -> Result<String, FmtError> {
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
                        None => return Err(FmtError::UnexpectedEndOfString),
                        Some('%') => out.push('%'),
                        Some('Y') => write!(out, "{:04}", date.0).unwrap_or(()),
                        Some('m') => write!(out, "{:02}", date.1).unwrap_or(()),
                        Some('d') => write!(out, "{:02}", date.2).unwrap_or(()),
                        Some('e') => write!(out, "{}", date.2).unwrap_or(()),
                        Some('H') => write!(out, "{:02}", time.0).unwrap_or(()),
                        Some('M') => write!(out, "{:02}", time.1).unwrap_or(()),
                        Some('S') => write!(out, "{:02}", time.2).unwrap_or(()),
                        Some('3') => {
                            write!(out, "{:03}", self.stamp.nano / 1_000_000).unwrap_or(())
                        }
                        Some('6') => write!(out, "{:06}", self.stamp.nano / 1_000).unwrap_or(()),
                        Some('9') => write!(out, "{:09}", self.stamp.nano).unwrap_or(()),
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
                        Some(c) => return Err(FmtError::InvalidFormatter(c)),
                    }
                }
                Some(c) => out.push(c),
            }
        }

        Ok(out)
    }

    /// Format `Datetime` according to RFC 3339 format.
    pub fn rfc3339(&self) -> String {
        self.format("%Y-%m-%dT%H:%M:%S%x").unwrap()
    }

    /// Format `Datetime` according to RFC 2822 format.
    pub fn rfc2822(&self) -> String {
        self.format("%a, %e %b %Y %H:%M:%S %z").unwrap()
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
        self.stamp.partial_cmp(&other.stamp)
    }
}

impl<'a> Ord for Datetime<'a> {
    fn cmp(&self, other: &Datetime) -> Ordering {
        self.stamp.cmp(&other.stamp)
    }
}

impl<'a> Add<Deltatime> for Datetime<'a> {
    type Output = Datetime<'a>;
    fn add(self, rhs: Deltatime) -> Self::Output {
        Datetime {
            tz: self.tz,
            stamp: self.stamp + rhs,
        }
    }
}

impl<'a> Sub<Deltatime> for Datetime<'a> {
    type Output = Datetime<'a>;
    fn sub(self, rhs: Deltatime) -> Self::Output {
        Datetime {
            tz: self.tz,
            stamp: self.stamp - rhs,
        }
    }
}

impl<'a> Sub<Datetime<'a>> for Datetime<'a> {
    type Output = Deltatime;
    fn sub(self, rhs: Datetime<'a>) -> Self::Output {
        self.stamp - rhs.stamp
    }
}

impl<'a> fmt::Debug for Datetime<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", self.rfc3339())
    }
}

/// Possible errors when creating a `Timezone`.
pub enum TzError {
    IOError(io::Error),
    InvalidTzFile,
    InvalidPosixTz,
    UnsupportedTzFile,
}

impl fmt::Debug for TzError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::error::Error;
        write!(fmt, "{}", self.description())
    }
}

impl fmt::Display for TzError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::error::Error;
        write!(fmt, "{}", self.description())
    }
}

impl error::Error for TzError {
    fn description(&self) -> &str {
        match *self {
            TzError::IOError(_) => "io error",
            TzError::InvalidTzFile => "invalid TZ file",
            TzError::InvalidPosixTz => "invalid POSIX TZ",
            TzError::UnsupportedTzFile => "unsupported TZ file",
        }
    }
}

impl std::convert::From<io::Error> for TzError {
    fn from(e: io::Error) -> Self {
        TzError::IOError(e)
    }
}

/// Possible errors when creating a `Datetime`.
pub enum InputError {
    InvalidMonth,
    InvalidDay,
    InvalidHour,
    InvalidMinute,
    InvalidSecond,
    InvalidNano,
    InvalidLeapSecond,
    InvalidFormat,
}

impl fmt::Debug for InputError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::error::Error;
        write!(fmt, "{}", self.description())
    }
}

impl fmt::Display for InputError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::error::Error;
        write!(fmt, "{}", self.description())
    }
}

impl error::Error for InputError {
    fn description(&self) -> &str {
        match *self {
            InputError::InvalidMonth => "invalid month",
            InputError::InvalidDay => "invalid day",
            InputError::InvalidHour => "invalid hour",
            InputError::InvalidMinute => "invalid minute",
            InputError::InvalidSecond => "invalid second",
            InputError::InvalidNano => "invalid nanosecond",
            InputError::InvalidLeapSecond => "invalid leap second",
            InputError::InvalidFormat => "invalid format",
        }
    }
}

/// Possible errors when formatting a `Datetime`.
pub enum FmtError {
    UnexpectedEndOfString,
    InvalidFormatter(char),
}

impl fmt::Debug for FmtError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::error::Error;
        write!(fmt, "{}", self.description())
    }
}

impl fmt::Display for FmtError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use std::error::Error;
        write!(fmt, "{}", self.description())
    }
}

impl error::Error for FmtError {
    fn description(&self) -> &str {
        match *self {
            FmtError::UnexpectedEndOfString => "unexpected end of string",
            FmtError::InvalidFormatter(_) => "invalid formatter",
        }
    }
}

// FIXME: is reading /usr/share/zoneinfo/leap-seconds.list
// a better way to store the leap information?
const NTP_TO_UNIX: i64 = 2208988800;
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

/// A delta of time used in `Datetime` arithmetic.
///
/// This represents a duration in time and can be used to shift `Datetime`
/// by a specified amount of time or as a result of comparing two
/// `Datetime`. Different types of `Deltatime` can be created and
/// each of those types affects `Datetime` differently. For example,
/// `Deltatime::seconds(86400)` is different from `Deltatime::days(1)`
/// because a `Deltatime` is dependant of the `Datetime` it applies to.
///
/// # Example
///
/// ```rust
/// let utc = hourglass::Timezone::utc();
/// let t = utc.datetime(2015, 6, 30, 0, 0, 0, 0).unwrap();
///
/// let add_86400_secs = t + hourglass::Deltatime::seconds(86400);
///
/// assert_eq!(add_86400_secs.date(), (2015, 6, 30));
/// assert_eq!(add_86400_secs.time(), (23, 59, 60, 0));
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Deltatime(Delta);

#[derive(Clone, Copy, Debug)]
enum Delta {
    Nanoseconds(i64),
    Seconds(i64),
    Days(i64),
}

impl Deltatime {
    /// Create a delta of `n` nanoseconds. Possible leap seconds are
    /// accounted for.
    pub fn nanoseconds(n: i64) -> Self {
        Deltatime(Delta::Nanoseconds(n))
    }

    /// Create a delta of `n` microseconds. Possible leap seconds are
    /// accounted for.
    pub fn microseconds(n: i64) -> Self {
        Deltatime(Delta::Nanoseconds(n * 1_000))
    }

    /// Create a delta of `n` milliseconds. Possible leap seconds are
    /// accounted for.
    pub fn milliseconds(n: i64) -> Self {
        Deltatime(Delta::Nanoseconds(n * 1_000_000))
    }

    /// Create a delta of `n` seconds. Possible leap seconds are
    /// accounted for.
    pub fn seconds(n: i64) -> Self {
        Deltatime(Delta::Seconds(n))
    }

    /// Create a delta of `n` minutes. Possible leap seconds are
    /// accounted for.
    pub fn minutes(n: i64) -> Self {
        Deltatime(Delta::Seconds(n * 60))
    }

    /// Create a delta of `n` hours. Possible leap seconds are accounted
    /// for.
    pub fn hours(n: i64) -> Self {
        Deltatime(Delta::Seconds(n * 3600))
    }

    /// Create a delta of `n` days. The time part of the shifted
    /// `Datetime` is not affected. This is a logical day, therefore,
    /// leap seconds are ignored.
    pub fn days(n: i64) -> Self {
        Deltatime(Delta::Days(n))
    }

    /// Returns the total number of nanoseconds contained in this delta.
    /// If the delta is created from `Deltatime::days`, the number
    /// of nanoseconds in a day is assumed to be `86400e9`.
    pub fn as_nanoseconds(&self) -> i64 {
        match self.0 {
            Delta::Nanoseconds(n) => n,
            Delta::Seconds(n) => n * 1_000_000_000,
            Delta::Days(n) => n * 86400 * 1_000_000_000,
        }
    }

    /// Returns the total number of microseconds contained in this delta.
    /// If the delta is created from `Deltatime::days`, the number
    /// of microseconds in a day is assumed to be `86400e6`.
    pub fn as_microseconds(&self) -> i64 {
        self.as_nanoseconds() / 1_000
    }

    /// Returns the total number of milliseconds contained in this delta.
    /// If the delta is created from `Deltatime::days`, the number
    /// of milliseconds in a day is assumed to be `86400e3`.
    pub fn as_milliseconds(&self) -> i64 {
        self.as_nanoseconds() / 1_000_000
    }

    /// Returns the total number of seconds contained in this delta.
    /// If the delta is created from `Deltatime::days`, the number
    /// of seconds in a day is assumed to be `86400`.
    pub fn as_seconds(&self) -> i64 {
        match self.0 {
            Delta::Nanoseconds(n) => n / 1_000_000_000,
            Delta::Seconds(n) => n,
            Delta::Days(n) => n * 86400,
        }
    }

    /// Returns the total number of minutes contained in this delta.
    pub fn as_minutes(&self) -> i64 {
        self.as_seconds() / 60
    }

    /// Returns the total number of hours contained in this delta.
    pub fn as_hours(&self) -> i64 {
        self.as_seconds() / 3_600
    }

    /// Returns the total number of days contained in this delta.
    pub fn as_days(&self) -> i64 {
        match self.0 {
            Delta::Nanoseconds(n) => n / 1_000_000_000 / 86400,
            Delta::Seconds(n) => n / 86400,
            Delta::Days(n) => n,
        }
    }

    /// Compare two `Deltatime`.
    fn cmp_delta(&self, rhs: &Deltatime) -> Ordering {
        self.as_nanoseconds().cmp(&rhs.as_nanoseconds())
    }
}

impl PartialEq<Deltatime> for Deltatime {
    fn eq(&self, other: &Deltatime) -> bool {
        self.cmp_delta(&other) == Ordering::Equal
    }
}

impl Eq for Deltatime {}

impl PartialOrd<Deltatime> for Deltatime {
    fn partial_cmp(&self, other: &Deltatime) -> Option<Ordering> {
        Some(self.cmp_delta(&other))
    }
}

impl Ord for Deltatime {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_delta(other)
    }
}

impl Neg for Deltatime {
    type Output = Deltatime;
    fn neg(self) -> Self::Output {
        Deltatime(match self.0 {
            Delta::Nanoseconds(n) => Delta::Nanoseconds(-n),
            Delta::Seconds(n) => Delta::Seconds(-n),
            Delta::Days(n) => Delta::Days(-n),
        })
    }
}

// C bindings & conv helpers

fn stamp_to_tm(sec: i64) -> libc::tm {
    let mut tm = libc::tm {
        tm_sec: 0,
        tm_min: 0,
        tm_hour: 0,
        tm_mday: 0,
        tm_mon: 0,
        tm_year: 0,
        tm_wday: 0,
        tm_yday: 0,
        tm_isdst: 0,
        // Unused
        tm_gmtoff: 0,
        tm_zone: sys::empty_tm_zone(),
    };
    unsafe { libc::gmtime_r(&sec, &mut tm) };
    tm
}

fn tm_to_stamp(tm: &libc::tm) -> i64 {
    // Thanks to Eric S. Raymond for releasing this function into the
    // public domain. I've tweaked it a bit but the algorithm's still
    // the same. libc's mktime function interprets the input tm as local
    // time, which is not what we want; timegm is not portable. The original
    // version allowed month overflow; I removed this behavior.
    const CUM_DAYS: &'static [i64; 12] = &[0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];

    let year = 1900 + tm.tm_year as i64;
    let mut result = (year - 1970) * 365 + CUM_DAYS[tm.tm_mon as usize];
    result += (year - 1968) / 4;
    result -= (year - 1900) / 100;
    result += (year - 1600) / 400;
    if ((year % 4 == 0 && year % 100 != 0) || year % 400 == 0) && tm.tm_mon < 2 {
        result -= 1;
    }
    result += tm.tm_mday as i64 - 1;
    result *= 24;
    result += tm.tm_hour as i64;
    result *= 60;
    result += tm.tm_min as i64;
    result *= 60;
    result += tm.tm_sec as i64;

    result
}


extern "C" {
    fn strptime(s: *const libc::c_char,
                fmt: *const libc::c_char,
                tm: *mut libc::tm)
                -> *const libc::c_char;
}

#[cfg(test)]
mod test {
    extern crate nom;
    extern crate libc;
    use super::{GenericDay, Type, TransRule, Deltatime, Timezone, Timespec};
    use super::{tm_to_stamp, stamp_to_tm, posixtz};
    use super::sys;

    #[test]
    fn test_datetime() {
        let utc = Timezone::utc();
        for &((y, m, d, h, mi, s, n), stamp) in &[((1970, 1, 1, 0, 0, 0, 0), 0),
                                                  ((1970, 1, 1, 1, 0, 0, 0), 3600),
                                                  ((2016, 1, 1, 0, 0, 0, 0), 1451606400),
                                                  ((1969, 12, 31, 23, 59, 59, 999_999_999), -1),
                                                  ((1969, 12, 31, 23, 59, 59, 0), -1),
                                                  ((1969, 12, 31, 23, 59, 58, 0), -2)] {
            let dt = utc.datetime(y, m, d, h, mi, s, n).unwrap();
            assert_eq!(dt.stamp.sec, stamp);
            assert_eq!(dt.stamp.leaping, false);
        }
    }

    #[test]
    fn test_leap_second() {
        let utc = Timezone::utc();
        let t = utc.datetime(2015, 6, 30, 23, 59, 59, 0).unwrap();
        let t_leap = utc.datetime(2015, 6, 30, 23, 59, 60, 0).unwrap();
        assert_eq!(t.stamp.leaping, false);
        assert_eq!(t_leap.stamp.leaping, true);
        assert_eq!(t.stamp.sec + 1, t_leap.stamp.sec);
        assert_eq!(t_leap.format("%S").unwrap(), "60");
        assert_eq!(t_leap.date(), (2015, 6, 30));
        assert_eq!(t_leap.time(), (23, 59, 60, 0));
        assert_eq!(t_leap.unix(), 1435708800);
        assert!(t_leap != t);
    }

    #[test]
    fn test_tz_projection() {
        let utc = Timezone::utc();
        let seoul = Timezone::new("Asia/Seoul").unwrap();
        let new_york = Timezone::new("America/New_York").unwrap();

        let t = utc.datetime(2016, 1, 15, 20, 0, 0, 0).unwrap();
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
        let t = paris.datetime(2006, 1, 2, 15, 4, 5, 123_456_789).unwrap();

        assert_eq!(t.format("%Y-%m-%dT%H:%M:%S").unwrap(),
                   "2006-01-02T15:04:05");
        assert_eq!(t.format("%3").unwrap(), "123");
        assert_eq!(t.format("%6").unwrap(), "123456");
        assert_eq!(t.format("%9").unwrap(), "123456789");
        assert_eq!(t.format("%z").unwrap(), "+0100");
        assert_eq!(t.format("%Z").unwrap(), "CET");
        assert_eq!(t.format("%w").unwrap(), "1");
        assert_eq!(t.format("%a").unwrap(), "Mon");
        assert_eq!(t.format("%A").unwrap(), "Monday");
        assert_eq!(t.format("%b").unwrap(), "Jan");
        assert_eq!(t.format("%B").unwrap(), "January");
        assert_eq!(t.format("%C").unwrap(), "20");
        assert_eq!(t.rfc3339(), "2006-01-02T15:04:05+01:00");
        assert_eq!(t.rfc2822(), "Mon, 2 Jan 2006 15:04:05 +0100");
    }

    #[test]
    fn test_parse() {
        let paris = Timezone::new("Europe/Paris").unwrap();
        let utc = Timezone::utc();

        let t = paris.parse("2006-01-02T15:04:05", "%Y-%m-%dT%H:%M:%S").unwrap();
        let t_utc = t.project(&utc);
        assert_eq!(t_utc.date(), (2006, 1, 2));
        assert_eq!(t_utc.time(), (14, 4, 5, 0));

        paris.parse("2006-01", &"%Y-%m-%d"[..5]).unwrap();
        paris.parse(&"2006-01-02"[..7], "%Y-%m").unwrap();
    }

    #[test]
    fn test_generic_day() {
        fn t(y: i32, m: i32, d: i32) -> libc::tm {
            let tm = libc::tm {
                tm_sec: 0,
                tm_min: 0,
                tm_hour: 0,
                tm_mday: d,
                tm_mon: m - 1,
                tm_year: y - 1900,
                tm_wday: 0,
                tm_yday: 0,
                tm_isdst: 0,
                tm_gmtoff: 0,
                tm_zone: sys::empty_tm_zone(),
            };
            // Make libc compute tm_wday.
            let stamp = tm_to_stamp(&tm);
            stamp_to_tm(stamp)
        }

        for &(ref gen, ref tm) in &[(GenericDay::Julian1 { jday: 59 }, t(2016, 2, 28)),
                                    (GenericDay::Julian1 { jday: 60 }, t(2016, 3, 1)),
                                    (GenericDay::Julian1 { jday: 365 }, t(2016, 12, 31)),
                                    (GenericDay::Julian1 { jday: 59 }, t(2015, 2, 28)),
                                    (GenericDay::Julian1 { jday: 60 }, t(2015, 3, 1)),
                                    (GenericDay::Julian1 { jday: 365 }, t(2015, 12, 31)),

                                    (GenericDay::Julian0 { jday: 58 }, t(2016, 2, 28)),
                                    (GenericDay::Julian0 { jday: 59 }, t(2016, 2, 29)),
                                    (GenericDay::Julian0 { jday: 60 }, t(2016, 3, 1)),
                                    (GenericDay::Julian0 { jday: 365 }, t(2016, 12, 31)),
                                    (GenericDay::Julian0 { jday: 58 }, t(2015, 2, 28)),
                                    (GenericDay::Julian0 { jday: 59 }, t(2015, 3, 1)),
                                    (GenericDay::Julian0 { jday: 364 }, t(2015, 12, 31)),

                                    (GenericDay::MWDRule {
                                        month: 1,
                                        week: 1,
                                        wday: 0,
                                    },
                                     t(2016, 1, 3)),
                                    (GenericDay::MWDRule {
                                        month: 1,
                                        week: 2,
                                        wday: 0,
                                    },
                                     t(2016, 1, 10)),
                                    (GenericDay::MWDRule {
                                        month: 1,
                                        week: 5,
                                        wday: 0,
                                    },
                                     t(2016, 1, 31)),
                                    (GenericDay::MWDRule {
                                        month: 1,
                                        week: 1,
                                        wday: 5,
                                    },
                                     t(2016, 1, 1)),
                                    (GenericDay::MWDRule {
                                        month: 1,
                                        week: 5,
                                        wday: 4,
                                    },
                                     t(2016, 1, 28)),
                                    (GenericDay::MWDRule {
                                        month: 1,
                                        week: 4,
                                        wday: 4,
                                    },
                                     t(2016, 1, 28))] {
            if gen != tm {
                panic!("{:?} != {:04}-{:02}-{:02}",
                       gen,
                       tm.tm_year,
                       tm.tm_mon,
                       tm.tm_mday);
            }
        }
    }

    #[test]
    fn test_trans_rule() {
        fn s(y: i32, mo: i32, d: i32, h: i32, m: i32, s: i32) -> i64 {
            let tm = libc::tm {
                tm_sec: s,
                tm_min: m,
                tm_hour: h,
                tm_mday: d,
                tm_mon: mo - 1,
                tm_year: y - 1900,
                tm_wday: 0,
                tm_yday: 0,
                tm_isdst: 0,
                tm_gmtoff: 0,
                tm_zone: sys::empty_tm_zone(),
            };
            tm_to_stamp(&tm)
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

    #[test]
    fn test_add_deltatime() {
        let utc = Timezone::utc();

        for &(dt, delta, res) in &[// nano
                                   ((2015, 6, 30, 23, 59, 59, 999_999_999),
                                    Deltatime::nanoseconds(2),
                                    (2015, 6, 30, 23, 59, 60, 1)),
                                   ((2015, 6, 30, 23, 59, 60, 1),
                                    Deltatime::nanoseconds(-2),
                                    (2015, 6, 30, 23, 59, 59, 999_999_999)),
                                   ((2015, 6, 30, 23, 59, 60, 200_000_000),
                                    Deltatime::nanoseconds(-300_000_000),
                                    (2015, 6, 30, 23, 59, 59, 900_000_000)),
                                   ((2015, 6, 30, 23, 59, 60, 1),
                                    Deltatime::nanoseconds(-1_000_000_002),
                                    (2015, 6, 30, 23, 59, 58, 999_999_999)),
                                   ((2016, 1, 1, 0, 0, 0, 0),
                                    Deltatime::nanoseconds(1_500_000_000),
                                    (2016, 1, 1, 0, 0, 1, 500_000_000)),
                                   ((2016, 1, 1, 0, 0, 1, 500_000_000),
                                    Deltatime::nanoseconds(-1_500_000_001),
                                    (2015, 12, 31, 23, 59, 59, 999_999_999)),
                                   ((2016, 1, 1, 0, 0, 1, 500_000_000),
                                    Deltatime::nanoseconds(-1_500_000_000),
                                    (2016, 1, 1, 0, 0, 0, 0)),
                                   ((2016, 1, 1, 0, 0, 0, 500_000_000),
                                    Deltatime::nanoseconds(500_000_001),
                                    (2016, 1, 1, 0, 0, 1, 1)),
                                   ((2016, 1, 1, 0, 0, 1, 1),
                                    Deltatime::nanoseconds(-500_000_001),
                                    (2016, 1, 1, 0, 0, 0, 500_000_000)),
                                   // regular -> leap
                                   ((2015, 6, 30, 23, 59, 59, 0),
                                    Deltatime::seconds(1),
                                    (2015, 6, 30, 23, 59, 60, 0)),
                                   ((2015, 6, 30, 23, 59, 60, 0),
                                    Deltatime::seconds(-1),
                                    (2015, 6, 30, 23, 59, 59, 0)),
                                   // leap -> regular
                                   ((2015, 6, 30, 23, 59, 60, 0),
                                    Deltatime::seconds(1),
                                    (2015, 7, 1, 0, 0, 0, 0)),
                                   ((2015, 7, 1, 0, 0, 0, 0),
                                    Deltatime::seconds(-1),
                                    (2015, 6, 30, 23, 59, 60, 0)),
                                   // regular -> regular
                                   ((2015, 6, 30, 23, 59, 59, 0),
                                    Deltatime::seconds(2),
                                    (2015, 7, 1, 0, 0, 0, 0)),
                                   ((2015, 7, 1, 0, 0, 0, 0),
                                    Deltatime::seconds(-2),
                                    (2015, 6, 30, 23, 59, 59, 0)),
                                   ((2015, 7, 1, 0, 0, 0, 0),
                                    Deltatime::seconds(1),
                                    (2015, 7, 1, 0, 0, 1, 0)),
                                   ((2015, 7, 1, 0, 0, 1, 0),
                                    Deltatime::seconds(-1),
                                    (2015, 7, 1, 0, 0, 0, 0)),
                                   ((2015, 6, 30, 23, 59, 59, 0),
                                    Deltatime::seconds(3),
                                    (2015, 7, 1, 0, 0, 1, 0)),
                                   ((2015, 7, 1, 0, 0, 1, 0),
                                    Deltatime::seconds(-3),
                                    (2015, 6, 30, 23, 59, 59, 0)),
                                   ((2012, 1, 1, 0, 0, 0, 0),
                                    Deltatime::seconds(126230402),
                                    (2016, 1, 1, 0, 0, 0, 0)), // 4 years, 2 leaps
                                   ((2016, 1, 1, 0, 0, 0, 0),
                                    Deltatime::seconds(-126230402),
                                    (2012, 1, 1, 0, 0, 0, 0)),
                                   ((1969, 12, 31, 23, 59, 59, 0),
                                    Deltatime::seconds(1),
                                    (1970, 1, 1, 0, 0, 0, 0)),
                                   ((1970, 1, 1, 0, 0, 0, 0),
                                    Deltatime::seconds(-1),
                                    (1969, 12, 31, 23, 59, 59, 0)),
                                   // leap -> leap
                                   ((2015, 6, 30, 23, 59, 60, 0),
                                    Deltatime::seconds(0),
                                    (2015, 6, 30, 23, 59, 60, 0)),
                                   ((2012, 6, 30, 23, 59, 60, 0),
                                    Deltatime::seconds(94608001),
                                    (2015, 6, 30, 23, 59, 60, 0)),
                                   ((2015, 6, 30, 23, 59, 60, 0),
                                    Deltatime::seconds(-94608001),
                                    (2012, 6, 30, 23, 59, 60, 0)),
                                   // days
                                   ((2016, 2, 29, 0, 0, 0, 0),
                                    Deltatime::days(1),
                                    (2016, 3, 1, 0, 0, 0, 0)),
                                   ((2016, 3, 1, 0, 0, 0, 0),
                                    Deltatime::days(-1),
                                    (2016, 2, 29, 0, 0, 0, 0)),
                                   ((2016, 1, 1, 0, 0, 0, 0),
                                    Deltatime::days(366),
                                    (2017, 1, 1, 0, 0, 0, 0)),
                                   ((2017, 1, 1, 0, 0, 0, 0),
                                    Deltatime::days(-366),
                                    (2016, 1, 1, 0, 0, 0, 0)),
                                   ((2015, 6, 30, 23, 59, 60, 0),
                                    Deltatime::days(1),
                                    (2015, 7, 2, 0, 0, 0, 0))] {
            let t = utc.datetime(dt.0, dt.1, dt.2, dt.3, dt.4, dt.5, dt.6).unwrap();
            let t = t + delta;
            assert_eq!(t.date(), (res.0, res.1, res.2));
            assert_eq!(t.time(), (res.3, res.4, res.5, res.6));
        }
    }

    #[test]
    fn test_delta_conversion() {
        let d = Deltatime::nanoseconds(1);
        assert_eq!(d.as_nanoseconds(), 1);
        assert_eq!(d.as_microseconds(), 0);
        assert_eq!(d.as_milliseconds(), 0);
        assert_eq!(d.as_seconds(), 0);
        assert_eq!(d.as_minutes(), 0);
        assert_eq!(d.as_hours(), 0);
        assert_eq!(d.as_days(), 0);

        let d = Deltatime::seconds(1);
        assert_eq!(d.as_nanoseconds(), 1_000_000_000);
        assert_eq!(d.as_microseconds(), 1_000_000);
        assert_eq!(d.as_milliseconds(), 1_000);
        assert_eq!(d.as_seconds(), 1);
        assert_eq!(d.as_minutes(), 0);
        assert_eq!(d.as_hours(), 0);
        assert_eq!(d.as_days(), 0);

        let d = Deltatime::days(1);
        assert_eq!(d.as_nanoseconds(), 1_000_000_000 * 86400);
        assert_eq!(d.as_microseconds(), 1_000_000 * 86400);
        assert_eq!(d.as_milliseconds(), 1_000 * 86400);
        assert_eq!(d.as_seconds(), 1 * 86400);
        assert_eq!(d.as_minutes(), 1440);
        assert_eq!(d.as_hours(), 24);
        assert_eq!(d.as_days(), 1);
    }

    #[test]
    fn test_cmp_datetimes() {
        let utc = Timezone::utc();
        let t0 = utc.datetime(2015, 1, 1, 0, 0, 0, 0).unwrap();
        let t1 = utc.datetime(2015, 1, 1, 0, 0, 0, 1).unwrap();
        assert!(t0 != t1);
        assert!(t0 < t1);
        assert!(t0 <= t1);

        let t0 = utc.datetime(2015, 1, 1, 0, 0, 0, 0).unwrap();
        let t1 = utc.datetime(2015, 1, 1, 0, 0, 1, 0).unwrap();
        assert!(t0 < t1);

        let t0 = utc.datetime(2015, 6, 30, 23, 59, 60, 1).unwrap();
        let t1 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();
        assert!(t0 < t1);
    }

    #[test]
    fn test_sub_datetimes() {
        let utc = Timezone::utc();
        let t0 = utc.datetime(2015, 1, 1, 0, 0, 0, 0).unwrap();
        let t1 = utc.datetime(2015, 1, 2, 0, 0, 0, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::days(1));
        assert_eq!(t0 - t1, Deltatime::days(-1));

        let t0 = utc.datetime(2015, 6, 30, 23, 59, 59, 0).unwrap();
        let t1 = utc.datetime(2015, 7, 1, 0, 0, 1, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(3));
        assert_eq!(t0 - t1, Deltatime::seconds(-3));

        let t0 = utc.datetime(2015, 6, 30, 23, 59, 59, 0).unwrap();
        let t1 = utc.datetime(2015, 6, 30, 23, 59, 60, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(1));
        assert_eq!(t0 - t1, Deltatime::seconds(-1));

        let t0 = utc.datetime(2015, 6, 30, 23, 59, 59, 0).unwrap();
        let t1 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(2));
        assert_eq!(t0 - t1, Deltatime::seconds(-2));

        let t0 = utc.datetime(2015, 6, 30, 23, 59, 60, 0).unwrap();
        let t1 = utc.datetime(2015, 7, 1, 0, 0, 1, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(2));
        assert_eq!(t0 - t1, Deltatime::seconds(-2));

        let t0 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();
        let t1 = utc.datetime(2015, 7, 1, 0, 0, 1, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(1));
        assert_eq!(t0 - t1, Deltatime::seconds(-1));

        let t0 = utc.datetime(2015, 6, 30, 23, 59, 60, 0).unwrap();
        let t1 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(1));
        assert_eq!(t0 - t1, Deltatime::seconds(-1));

        let t0 = utc.datetime(2015, 6, 30, 23, 59, 60, 0).unwrap();
        let t1 = utc.datetime(2015, 6, 30, 23, 59, 60, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(0));
        assert_eq!(t0 - t1, Deltatime::seconds(0));

        let t0 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();
        let t1 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();
        assert_eq!(t1 - t0, Deltatime::seconds(0));
        assert_eq!(t0 - t1, Deltatime::seconds(0));
    }

    #[test]
    fn test_posixtz() {
        fn mwd(m: i32, w: i32, d: i32) -> GenericDay {
            GenericDay::MWDRule {
                month: m,
                week: w,
                wday: d,
            }
        }
        fn std(off_h: i32, abbr: &str) -> Type {
            Type {
                off: off_h * 3600,
                is_dst: false,
                abbr: abbr.to_owned(),
            }
        }
        fn dst(off_h: i32, abbr: &str) -> Type {
            Type {
                off: off_h * 3600,
                is_dst: true,
                abbr: abbr.to_owned(),
            }
        }

        for &(sample, ref expected) in &[("AEST-10AEDT,M10.1.0,M4.1.0/3",
                                          TransRule::Alternate {
                                             dst_start: mwd(10, 1, 0),
                                             dst_stime: 2 * 3600,
                                             dst_end: mwd(4, 1, 0),
                                             dst_etime: 3 * 3600,
                                             std: std(10, "AEST"),
                                             dst: dst(11, "AEDT"),
                                         }),
                                         ("CST6CDT,M4.1.0,M10.5.0",
                                          TransRule::Alternate {
                                             dst_start: mwd(4, 1, 0),
                                             dst_stime: 2 * 3600,
                                             dst_end: mwd(10, 5, 0),
                                             dst_etime: 2 * 3600,
                                             std: std(-6, "CST"),
                                             dst: dst(-5, "CDT"),
                                         }),
                                         ("MSK-3", TransRule::Fixed(std(3, "MSK"))),
                                         ("ART3", TransRule::Fixed(std(-3, "ART"))),
                                         ("WET0WEST,M3.5.0/1,M10.5.0",
                                          TransRule::Alternate {
                                             dst_start: mwd(3, 5, 0),
                                             dst_stime: 1 * 3600,
                                             dst_end: mwd(10, 5, 0),
                                             dst_etime: 2 * 3600,
                                             std: std(0, "WET"),
                                             dst: dst(1, "WEST"),
                                         })] {
            match posixtz(sample) {
                nom::IResult::Done(_, ref r) if *r == *expected => (),
                _ => panic!("{} != {:?}", sample, expected),
            }
        }
    }

    #[test]
    fn test_datetime_timespec_conv() {
        let t = Timespec::now();
        let utc = Timezone::utc();
        let utc2 = Timezone::fixed(2 * 3600);
        let dt_utc = t.to_datetime(&utc);
        let dt_utc2 = t.to_datetime(&utc2);

        let t0 = dt_utc.to_timespec();
        let t2 = dt_utc2.to_timespec();
        assert_eq!(t, t0);
        assert_eq!(t0, t2);
    }
}

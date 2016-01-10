//! `tzdata` uses the IANA Time Zone Database to provide conversion between timezones.
extern crate time;

mod parse;

pub use time::*;
use std::rc::Rc;
use std::io;

/// A named timezone from the [`IANA Time Zone Database`](https://www.iana.org/time-zones)
///
/// # Example
///
/// ```rust
/// use  tzdata::*;
///
/// let now = now_utc();
/// for tzname in &["Europe/Paris", "America/New_York", "Asia/Seoul"] {
///     let tz = Timezone::new(tzname).unwrap();
///     let now = tz.localize(now);
///     println!("now is {} in {}", now.rfc3339(), tz.name);
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

    /// Project a `Tm` from UTC into the `Timezone`.
    /// Panics if not in UTC timezone.
    pub fn localize(&self, t: time::Tm) -> time::Tm {
        assert_eq!(t.tm_utcoff, 0);

        let tspec = t.to_timespec();
        let idx = match self.trans.binary_search_by(|t| t.utc.cmp(&tspec.sec)) {
            Err(0) => return t, // FIXME?
            Err(i) => i - 1,
            Ok(i) => i,
        };

        let off = self.trans[idx].ttype.utc_off_sec;;
        let mut t = t + time::Duration::seconds(off as i64);
        t.tm_utcoff = off;
        t
    }
}

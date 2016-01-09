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

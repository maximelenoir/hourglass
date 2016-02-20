use super::{Timespec, Deltatime};
use std::iter::Iterator;
use std::thread;
use std::time;
use std::cmp;

/// An iterator used to schedule execution at regular time interval.
///
/// `Every` allows to create loops whose bodies will be run at fixed
/// interval. If the execution of the body takes longer than the requested
/// step, the next iteration is scheduled right away. The precision of
/// the interval is platform-dependant.
///
/// ```rust
/// use hourglass::{Timezone, Deltatime, Timespec, Every};
///
/// let paris = Timezone::new("Europe/Paris").unwrap();
/// let until = Timespec::now() + Deltatime::seconds(5);
///
/// for t in Every::until(Deltatime::seconds(1), until) {
///     println!("it is {} in Paris", t.to_datetime(&paris).format("%H:%M:%S").unwrap());
/// }
/// ```
pub struct Every {
    step: Deltatime,
    next: Timespec,
    until: Option<Timespec>,
}

impl Every {
    /// Create a new `Every` iterator that will never end. Each iteration
    /// will be started every `step` if possible.
    pub fn new(step: Deltatime) -> Every {
        Every {
            step: step,
            next: Timespec::now(),
            until: None,
        }
    }

    /// Create a new `Every` iterator that will end when `until` is
    /// reached. Each iteration will be started every `step` if possible.
    /// If the end of the current iteration is reached before `until`,
    /// a new iteration will be rearmed even if `until` has been reached
    /// at the beginning of the next iteration, i.e. `Every` will not
    /// sleep in vain and will either stop the iteration right away or
    /// sleep and schedule a new iteration.
    pub fn until(step: Deltatime, until: Timespec) -> Every {
        Every {
            step: step,
            next: Timespec::now(),
            until: Some(until),
        }
    }
}

impl Iterator for Every {
    type Item = Timespec;
    fn next(&mut self) -> Option<Self::Item> {
        let now = Timespec::now();

        if let Some(t) = self.until {
            if now >= t {
                return None;
            }
        }

        if now >= self.next {
            self.next = now + self.step;
            return Some(now);
        }

        let wait = self.next - now;
        let sec = wait.as_seconds();
        let nano = wait.as_nanoseconds() - sec * 1_000_000_000;
        let dur = time::Duration::new(sec as u64, nano as u32);
        thread::sleep(dur);

        // Get the new now
        let now = Timespec::now();
        self.next = now + self.step;
        Some(now)
    }
}

/// An iterator over a period of time.
///
/// `Range` provides an iterator that will go through `Timespec` values
/// in a given range. A step argument, defined as a `Deltatime`, is used
/// to control the pace of the iteration. `Range` offers support for
/// both bounded and unbounded iterations.
pub struct Range {
    step: Deltatime,
    next: Timespec,
    until: Option<Timespec>,
    cont: cmp::Ordering,
}

impl Range {
    /// Create a new `Range` that will iterate from `start` to `end` with
    /// `step` increments. The first iteration will yield `start`. If
    /// `step` is a negative value, `Range` will yield decreasing values
    /// of `Timespec` down to `end`. If `step` is positive, `Range` will
    /// yield increasing values of `Timespec` up to `end`. If `step` is
    /// zero, `start` will be returned forever. If `end` cannot be reached
    /// from `start` with the given `step` (e.g. `end` is set after `start`
    /// with a negative `step`), the iterator will not returned any
    /// value. The upper bound is always excluded.
    pub fn new(start: Timespec, end: Timespec, step: Deltatime) -> Range {
        Range {
            step: step,
            next: start,
            until: Some(end),
            cont: if step > Deltatime::nanoseconds(0) {
                cmp::Ordering::Less
            } else {
                cmp::Ordering::Greater
            },
        }
    }

    /// Create a new `Range` that will iterate indefinitely from `start`,
    /// with `step` increments. The first iteration will yield `start`. If
    /// `step` is a negative value, `Range` will yield decreasing
    /// values of `Timespec`. If `step` is positive, `Range` will yield
    /// increasing values of `Timespec`. If `step` is zero, `start`
    /// will be returned forever. The upper bound is always excluded.
    pub fn from(start: Timespec, step: Deltatime) -> Range {
        Range {
            step: step,
            next: start,
            until: None,
            cont: cmp::Ordering::Equal, // Ignored
        }
    }
}

impl Iterator for Range {
    type Item = Timespec;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next;
        self.next = self.next + self.step;

        // Check if the iteration should stop.
        match self.until {
            None => Some(next),
            Some(until) => {
                if next.cmp(&until) == self.cont {
                    Some(next)
                } else {
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::super::{Timespec, Deltatime};
    use super::Range;

    #[test]
    fn test_range() {
        let t0 = Timespec::unix(1456000227, 0).unwrap();
        let t1 = Timespec::unix(1456000228, 0).unwrap();
        let t2 = Timespec::unix(1456000229, 0).unwrap();
        let t3 = Timespec::unix(1456000230, 0).unwrap();

        let mut r = Range::new(t0, t1, Deltatime::seconds(1));
        assert_eq!(r.next(), Some(t0));
        assert_eq!(r.next(), None);

        let mut r = Range::new(t0, t3, Deltatime::seconds(2));
        assert_eq!(r.next(), Some(t0));
        assert_eq!(r.next(), Some(t2));
        assert_eq!(r.next(), None);

        let mut r = Range::new(t1, t0, Deltatime::seconds(1));
        assert_eq!(r.next(), None);

        let mut r = Range::new(t1, t0, -Deltatime::seconds(1));
        assert_eq!(r.next(), Some(t1));
        assert_eq!(r.next(), None);

        let mut r = Range::new(t3, t0, -Deltatime::seconds(2));
        assert_eq!(r.next(), Some(t3));
        assert_eq!(r.next(), Some(t1));
        assert_eq!(r.next(), None);

        let mut r = Range::new(t0, t1, -Deltatime::seconds(1));
        assert_eq!(r.next(), None);
    }

    #[test]
    fn test_range_unbounded() {
        let t0 = Timespec::unix(1456000227, 0).unwrap();
        let t1 = Timespec::unix(1456009999, 0).unwrap();

        let unbounded = Range::from(t0, Deltatime::seconds(1));
        let bounded = Range::new(t0, t1, Deltatime::seconds(1));
        for (tu, tb) in unbounded.zip(bounded) {
            assert_eq!(tu, tb);
        }

        let unbounded = Range::from(t1, -Deltatime::seconds(1));
        let bounded = Range::new(t1, t0, -Deltatime::seconds(1));
        for (tu, tb) in unbounded.zip(bounded) {
            assert_eq!(tu, tb);
        }
    }
}

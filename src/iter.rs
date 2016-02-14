use super::{Timespec, Deltatime};
use std::iter::Iterator;
use std::thread;
use std::time;

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

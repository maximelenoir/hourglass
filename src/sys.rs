// from https://github.com/rust-lang-deprecated/time/

#[cfg(not(target_os = "macos"))]
mod unix {
    use libc;
    use std::ptr;

    pub fn get_time() -> (i64, i32) {
        let mut tv = libc::timespec { tv_sec: 0, tv_nsec: 0 };
        unsafe { libc::clock_gettime(libc::CLOCK_REALTIME, &mut tv); }
        (tv.tv_sec as i64, tv.tv_nsec as i32)
    }

    pub fn empty_tm_zone<T>() -> *const T {
        ptr::null()
    }
}


#[cfg(target_os = "macos")]
mod mac {
    use libc;
    use std::ptr;

    pub fn get_time() -> (i64, i32) {
        let mut tv = libc::timeval { tv_sec: 0, tv_usec: 0 };
        unsafe { libc::gettimeofday(&mut tv, ptr::null_mut()); }
        (tv.tv_sec as i64, tv.tv_usec * 1000)
    }

    pub fn empty_tm_zone<T>() -> *mut T {
        ptr::null_mut()
    }
}


#[cfg(target_os = "macos")]
pub use self::mac::*;
#[cfg(not(target_os = "macos"))]
pub use self::unix::*;

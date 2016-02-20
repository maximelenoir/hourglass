# hourglass

Timezone-aware datetime library for the Rust programming language ([doc](https://maximelenoir.github.io/hourglass/hourglass))

[![Build Status](https://travis-ci.org/maximelenoir/hourglass.svg?branch=master)](https://travis-ci.org/maximelenoir/hourglass)
[![Crate Version](https://img.shields.io/crates/v/hourglass.svg)](https://crates.io/crates/hourglass)

`hourglass` provides support for timezone, datetime arithmetic and take care
of subtleties related to time handling, like leap seconds.

## Usage

Add the following in your `Cargo.toml`:

```toml
[dependencies]
hourglass = "0.*"
```

And put this in your crate root:

```rust
extern crate hourglass;
```

## Overview

### Timezone

Because a datetime without a timezone is ambiguous and error-prone, `hourglass`
only exposes a `Datetime` that is timezone-aware. The creation of a `Timezone`
is the entry point of the API. `hourglass` provides several way of creating
a `Timezone`:

```rust
use hourglass::Timezone;

let utc = Timezone::utc();
let local = Timezone::local().unwrap();
let paris = Timezone::new("Europe/Paris").unwrap();
let fixed = Timezone::fixed(-5 * 3600);
```

A `Datetime` is created for a specific timezone and can be projected in another
timezone:

```rust
use hourglass::Timezone;

let utc = Timezone::utc();
let paris = Timezone::new("Europe/Paris").unwrap();

// Create a `Datetime` corresponding to midnight in Paris timezone...
let t = paris.datetime(2015, 12, 25, 0, 0, 0, 0).unwrap();
// ... and project it into UTC timezone.
let t_utc = t.project(&utc);
assert_eq!(t_utc.date(), (2015, 12, 24));
assert_eq!(t_utc.time(), (23, 0, 0, 0));
```

### Arithmetic

`Datetime` arithmetic is performed with a `Deltatime`. Several granularities
are available when handling `Deltatime` and will yield different results:

```rust
use hourglass::{Timezone, Deltatime};

let utc = Timezone::utc();
let t = utc.datetime(2015, 6, 30, 0, 0, 0, 0).unwrap();
let t_plus_1_day = t + Deltatime::days(1);
let t_plus_86400_sec = t + Deltatime::seconds(86400);

assert_eq!(t_plus_1_day.date(), (2015, 7, 1));
// One leap second was inserted this day.
assert_eq!(t_plus_86400_sec.date(), (2015, 6, 30));
assert_eq!(t_plus_86400_sec.time(), (23, 59, 60, 0));
```

Two `Datetime` can also be compared:

```rust
use hourglass::{Timezone, Deltatime};

let utc = Timezone::utc();
let t0 = utc.datetime(2015, 6, 30, 0, 0, 0, 0).unwrap();
let t1 = utc.datetime(2015, 7, 1, 0, 0, 0, 0).unwrap();

assert_eq!(t0 < t1, true);
assert_eq!(t0 >= t1, false);
assert_eq!(t1 == t1, true);
assert_eq!(t1 - t0, Deltatime::seconds(86401));
```

### Iterators

`hourglass` also provides the `Every` iterator for scheduling a loop
body execution at regular time interval:

```rust
use hourglass::{Timezone, Deltatime, Timespec, Every};

let paris = Timezone::new("Europe/Paris").unwrap();
let until = Timespec::now() + Deltatime::seconds(5);

for t in Every::until(Deltatime::seconds(1), until) {
    println!("it is {} in Paris", t.to_datetime(&paris).format("%H:%M:%S").unwrap());
}
```

The `Range` iterator can be used to iterate over a range of `Timespec`:

```rust
use hourglass::{Deltatime, Timespec, Range};

let now = Timespec::now();
let then = now + Deltatime::minutes(1);

for t in Range::new(now, then, Deltatime::seconds(1)) {
    println!("tick {}", t.seconds());
}
```

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
let t = paris.datetime(2015, 12, 25, 0, 0, 0, 0);
// ... and project it into UTC timezone.
let t_utc = t.project(&utc);
assert_eq!(t_utc.date(), (2015, 12, 24));
assert_eq!(t_utc.time(), (23, 0, 0, 0));
```

`Datetime` arithmetic is performed with a `Deltatime`. Several granularities
are available when handling `Deltatime` and will yield different results:

```rust
use hourglass::{Timezone, Deltatime};

let utc = Timezone::utc();
let t = utc.datetime(2015, 6, 30, 0, 0, 0, 0);
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
let t0 = utc.datetime(2015, 6, 30, 0, 0, 0, 0);
let t1 = utc.datetime(2015, 7, 1, 0, 0, 0, 0);

assert_eq!(t0 < t1, true);
assert_eq!(t0 >= t1, false);
assert_eq!(t1 == t1, true);
assert_eq!(t1 - t0, Deltatime::seconds(86401));
```

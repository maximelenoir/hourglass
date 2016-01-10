# tzdata-rs

Timezone library for the Rust programming language ([doc](https://maximelenoir.github.io/tzdata-rs/tzdata))

[![Build Status](https://travis-ci.org/maximelenoir/tzdata-rs.svg?branch=master)](https://travis-ci.org/maximelenoir/tzdata-rs)
[![Crate Version](https://img.shields.io/crates/v/tzdata.svg)](https://crates.io/crates/tzdata)

## Usage

Add the following in your `Cargo.toml`:

```toml
[dependencies]
tzdata = "0.*"
```

And put this in your crate root:

```rust
extern crate tzdata;
```
## Example

The library provides basic support for timezone conversion.

```rust
let utc = tzdata::Timezone::utc();
let now = utc.now();

for tzname in &["Europe/Paris", "America/New_York", "Asia/Seoul"] {
    let tz = tzdata::Timezone::new(tzname).unwrap();
    let now = now.project(&tz);
    println!("it is now {:?} in {}", now, tz.name);
}
```

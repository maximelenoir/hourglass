# tzdata-rs
Timezone library for the Rust programming language

The library provides basic support for timezone conversion.

```rust
let now = now_utc();
for tzname in &["Europe/Paris", "America/New_York", "Asia/Seoul"] {
    let tz = Timezone::new(tzname).unwrap();
    let now = tz.localize(now);
    println!("now is {} in {}", now.rfc3339(), tz.name);
}
```

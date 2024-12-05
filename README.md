# jiff-cron [![Rust](https://github.com/jiff-cron/jiff-cron/workflows/Rust/badge.svg)](https://github.com/jiff-cron/jiff-cron/actions) [![dependency status](https://deps.rs/repo/github/jiff-cron/jiff-cron/status.svg)](https://deps.rs/repo/github/jiff-cron/jiff-cron) [![](https://img.shields.io/crates/v/jiff-cron.svg)](https://crates.io/crates/jiff-cron) [![](https://docs.rs/jiff-cron/badge.svg)](https://docs.rs/jiff-cron)

A cron expression parser built with `jiff`.

## Example

```rust
use jiff_cron::{jiff::tz::TimeZone, Schedule};
use std::str::FromStr;

fn main() {
  //               sec  min   hour   day of month   month   day of week   year
  let expression = "0   30   9,12,15     1,15       May-Aug  Mon,Wed,Fri  2018/2";
  let schedule = Schedule::from_str(expression).unwrap();
  println!("Upcoming fire times:");
  for datetime in schedule.upcoming(TimeZone::UTC).take(10) {
    println!("-> {}", datetime);
  }
}

/*
Upcoming fire times:
-> 2018-06-01 09:30:00 UTC
-> 2018-06-01 12:30:00 UTC
-> 2018-06-01 15:30:00 UTC
-> 2018-06-15 09:30:00 UTC
-> 2018-06-15 12:30:00 UTC
-> 2018-06-15 15:30:00 UTC
-> 2018-08-01 09:30:00 UTC
-> 2018-08-01 12:30:00 UTC
-> 2018-08-01 15:30:00 UTC
-> 2018-08-15 09:30:00 UTC
*/
```

## Installation

Add to your `Cargo.toml`:

```toml
jiff-cron = "0.1.1"
```

You can enable optional [`serde`](https://docs.rs/crate/serde) support
via [crate feature toggle](https://docs.rs/crate/jiff-cron/latest/features).

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or https://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or https://opensource.org/licenses/MIT)
  at your option.

## Minimum supported Rust version (MSRV)

This crate requires Rust 1.80.0 or newer.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you shall be dual licensed as above, without any
additional terms or conditions.

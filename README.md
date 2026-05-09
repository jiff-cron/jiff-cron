# jiff-cron [![Rust](https://github.com/jiff-cron/jiff-cron/workflows/Rust/badge.svg)](https://github.com/jiff-cron/jiff-cron/actions) [![dependency status](https://deps.rs/repo/github/jiff-cron/jiff-cron/status.svg)](https://deps.rs/repo/github/jiff-cron/jiff-cron) [![](https://img.shields.io/crates/v/jiff-cron.svg)](https://crates.io/crates/jiff-cron) [![](https://docs.rs/jiff-cron/badge.svg)](https://docs.rs/jiff-cron)

A cron expression parser built with `jiff`.

## Examples

```rust
use std::str::FromStr;

use jiff_cron::{jiff::tz::TimeZone, Schedule};

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

→ 2018-06-01T09:30:00+00:00[UTC]
→ 2018-06-01T12:30:00+00:00[UTC]
→ 2018-06-01T15:30:00+00:00[UTC]
→ 2018-06-15T09:30:00+00:00[UTC]
→ 2018-06-15T12:30:00+00:00[UTC]
→ 2018-06-15T15:30:00+00:00[UTC]
→ 2018-08-01T09:30:00+00:00[UTC]
→ 2018-08-01T12:30:00+00:00[UTC]
→ 2018-08-01T15:30:00+00:00[UTC]
→ 2018-08-15T09:30:00+00:00[UTC]

*/
```

### DST behavior

`jiff` also handles daylight savings gaps and folding appropriately:

```rust
use std::str::FromStr;

use jiff_cron::{
    jiff::{civil::date, tz::TimeZone},
    Schedule,
};

fn main() {
    let expression = "0 0 * * * * *";
    let schedule = Schedule::from_str(expression).unwrap();
    let after_datetime = date(2022, 11, 5)
        .at(23, 30, 0, 0)
        .in_tz("America/Chicago")
        .unwrap();
    println!("Upcoming fire times:");
    for datetime in schedule.after(&after_datetime).take(5) {
        println!("-> {}", datetime);
    }
}

/*

Upcoming fire times:

→ 2022-11-06T00:00:00-05:00[America/Chicago]
→ 2022-11-06T01:00:00-05:00[America/Chicago]
→ 2022-11-06T01:00:00-06:00[America/Chicago]
→ 2022-11-06T02:00:00-06:00[America/Chicago]
→ 2022-11-06T03:00:00-06:00[America/Chicago]

*/
```

## Installation

Add to your `Cargo.toml`:

```toml
jiff-cron = "0.2.0"
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

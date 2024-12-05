#![deny(rust_2018_idioms)]
#![deny(rustdoc::broken_intra_doc_links)]
#![allow(clippy::needless_doctest_main)]
//! A cron expression parser and schedule explorer built with jiff.
//!
//! # Example
//!
//! ```rust
//! use std::str::FromStr;
//!
//! use jiff_cron::{jiff::tz::TimeZone, Schedule};
//!
//! fn main() {
//!     //               sec  min   hour   day of month   month   day of week   year
//!     let expression = "0   30   9,12,15     1,15       May-Aug  Mon,Wed,Fri  2018/2";
//!     let schedule = Schedule::from_str(expression).unwrap();
//!     println!("Upcoming fire times:");
//!     for datetime in schedule.upcoming(TimeZone::UTC).take(10) {
//!         println!("-> {}", datetime);
//!     }
//! }
//!
//! /*
//! Upcoming fire times:
//! -> 2018-06-01 09:30:00 UTC
//! -> 2018-06-01 12:30:00 UTC
//! -> 2018-06-01 15:30:00 UTC
//! -> 2018-06-15 09:30:00 UTC
//! -> 2018-06-15 12:30:00 UTC
//! -> 2018-06-15 15:30:00 UTC
//! -> 2018-08-01 09:30:00 UTC
//! -> 2018-08-01 12:30:00 UTC
//! -> 2018-08-01 15:30:00 UTC
//! -> 2018-08-15 09:30:00 UTC
//! */
//! ```
//!
//! # Installation
//!
//! Add to your `Cargo.toml`:
//!
//! ```toml
//! jiff-cron = "0.1.1"
//! ```
//!
//! You can enable optional [`serde`](https://docs.rs/crate/serde) support
//! via [crate feature toggle](https://docs.rs/crate/jiff-cron/latest/features).

/// Error types used by this crate.
pub mod error;

mod ordinal;
mod parsing;
mod queries;
mod schedule;
mod specifier;
mod time_unit;

pub use jiff;

pub use crate::{
    schedule::{OwnedScheduleIterator, Schedule, ScheduleIterator},
    time_unit::TimeUnitSpec,
};

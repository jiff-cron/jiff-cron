# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- next-header -->

## [Unreleased] <!-- release-date -->

### BREAKING CHANGES

- Re-define `Schedule` equality in terms of **parsed representation**.
  Users depending on **source string** equality must migrate to comparing `a.source() == b.source()`. (https://github.com/jiff-cron/jiff-cron/issues/9, https://github.com/maxcountryman/jiff-cron/pull/10) by @LeoniePhiline
- Replace `once_cell::sync::Lazy` by `std::sync::LazyLock` implementation.
  The MSRV has been lifted to Rust 1.80.0. (https://github.com/jiff-cron/jiff-cron/issues/7, https://github.com/jiff-cron/jiff-cron/pull/12) by @LeoniePhiline

### Added

- Configure `rustfmt` for consistent code style (https://github.com/jiff-cron/jiff-cron/pull/4) by @maxcountryman
- Re-export `jiff` (https://github.com/jiff-cron/jiff-cron/commit/7504ab9727d55733096fd596b96d25bad9ddfd5c) by @LeoniePhiline
- Insert dependency status badge (https://github.com/jiff-cron/jiff-cron/commit/36398ec995a8ed97940ed8592956a3bc3c469c99) by @LeoniePhiline
- Keep a changelog and configure `cargo-release` (https://github.com/jiff-cron/jiff-cron/issues/6, https://github.com/jiff-cron/jiff-cron/pull/27) by @LeoniePhiline

### Changed

- Clean up left over comments from the migration to `jiff` (https://github.com/jiff-cron/jiff-cron/pull/5) by @LeoniePhiline
- Document shared ownership (https://github.com/jiff-cron/jiff-cron/commit/e103e0219eb989fb8c8ac49efdebbe31d0654f83) by @LeoniePhiline
- Declare broader dependency versions (https://github.com/jiff-cron/jiff-cron/pull/20) by @LeoniePhiline
- Update links to point to the `jiff-cron` GitHub organization (https://github.com/jiff-cron/jiff-cron/commit/1eff14a82e19a305d684044aa11e92500e4a6b43) by @maxcountryman

### Fixed

- Avoid running CI workflows twice (https://github.com/jiff-cron/jiff-cron/commit/398054060fce88b92883e3875328ca18da9364ed) by @maxcountryman

## [0.1.1] - 2024-11-01

### Added

- Implement efficient conversion from `String` (https://github.com/maxcountryman/jiff-cron/commit/ef8e33ab6822a9ea72669629139e264179dd213f, https://github.com/zslayton/cron/pull/128) by @LeoniePhiline
- Implement optimized `Serialize` and `Deserialize` for Schedule (https://github.com/maxcountryman/jiff-cron/commit/c5d5589936aef5c6bca17f0c86030e7a98a8dc42, https://github.com/zslayton/cron/pull/129) by @LeoniePhiline

### Changed

- Run `cargo fmt` and fix all reports (https://github.com/maxcountryman/jiff-cron/commit/c491880275693cfbfc596caa3701304fe5a1775b, https://github.com/zslayton/cron/pull/123) by @bombsimon

### Fixed

- Fix backwards iteration when inital time has milliseconds (https://github.com/maxcountryman/jiff-cron/commit/e2fb9581a2626d95bfa32a1e31e0ba80c2a4cf21, https://github.com/zslayton/cron/pull/112) by @juancampa
- Patterns with future years should not limit the day and month range (https://github.com/maxcountryman/jiff-cron/commit/bc0778769853ca07f4a211c41f61cc86f51cd42d, https://github.com/zslayton/cron/pull/116) by @AhmedSoliman
- fix: Don't accept invalid step for `Period` (https://github.com/maxcountryman/jiff-cron/commit/cabee0f36eec4faa34ebe3780046516d4a97a41b, https://github.com/zslayton/cron/pull/122) by @bombsimon

<!-- next-url -->
[Unreleased]: https://github.com/LeoniePhiline/async-mailer/compare/v0.1.1...HEAD
[0.1.0]: https://github.com/LeoniePhiline/async-mailer/releases/tag/v0.1.1

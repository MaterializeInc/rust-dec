# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog], and this crate adheres to [Semantic
Versioning].

## Unreleased

* Add the `OrderedDecimal` wrapper type to imbue `Decimal64` and `Decimal128`
  with implementations of `Ord` and `Hash`, akin to
  `ordered_float::OrderedFloat`.

* Add associated constants for zero and NaN to each floating-point decimal
  type. The full list of added constants is:

  * `Decimal32::ZERO`
  * `Decimal32::NAN`
  * `Decimal64::ZERO`
  * `Decimal64::NAN`
  * `Decimal128::ZERO`
  * `Decimal128::NAN`

* Remove the `Decimal32::zero`, `Decimal64::zero`, and `Decimal128::zero`
  methods. Use either the `ZERO` associated constant or the `Default`
  implementation instead.

* Mark `Decimal32::from_ne_bytes`, `Decimal64::from_ne_bytes`, and
  `Decimal128::from_ne_bytes` as `const fn`s.

## 0.1.2 - 2020-02-01

* Correct documentation links in README, again.

## 0.1.1 - 2020-02-01

* Correct documentation links in README.
* Implement `Hash` for the `Class`, `Rounding` and `Status` types.
* Include fields in `fmt::Debug` output for `Status`.

## 0.1.0 - 2020-01-31

Initial release.

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html

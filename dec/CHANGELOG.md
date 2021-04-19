# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog], and this crate adheres to [Semantic
Versioning].

## Unreleased

* Remove the `arbitrary-precision` feature. The arbitrary-precision `Decimal`
  type is now always compiled.

* Add the `Decimal::infinity`, `Decimal::nan`, `Decimal::rescale`, and
  `Decimal::to_standard_notation_string` methods.

* Implement `From<u32>`, `From<u64>`, `From<i32>`, `From<i64>`, `From<usize>`,
  `From<isize>`, `PartialOrd` and `PartialEq` for `Decimal`.

* Enable using `OrderedDecimal` with the `Decimal` type.

* Add the `Context::set_status` method.

* Implement `BitAnd`, `BitAndAssign`, `BitOr`, and `BitOrAssign` for `Status`.


## 0.3.3 - 2021-03-10

* Fix bug that could cause `to_standard_notation_string` to misplace the decimal
  point in its returned value.

## 0.3.2 - 2021-03-10

* Add the `set_exponent` method to `Context::<Decimal64>` an
  `Context::<Decimal128>`.

* Add the `rescale` method to `Context::<Decimal64>` and
  `Context::<Decimal128>`, which represents an equivalent number with as many of
  the same significant digits as possible.

* Add the `coefficient_digits` method to `Decimal64` and `Decimal128` to return
  a number's coefficient's individual digits.

  Other methods largely obviate this method's uses, e.g. `coefficient`, but we
  provide it to expose more of `libdecnumber`'s API.

* Add the `to_standard_notation_string` method to `Decimal64` and `Decimal128`
  to generate string representations of digits that, for example, avoid the
  truncation in scientific notation.

## 0.3.1 - 2021-02-25

* Add the `coefficient` method to `Decimal32`, `Decimal64`, and `Decimal128`,
  which return the unscaled coefficient of the decimal as an `i32`, `i64`, or
  `i128`, respectively.

## 0.3.0 - 2021-02-11

* Implement `From<i64>` and `From<u64>` for `Decimal128`.

* Add the `from_i64` and `from_u64` methods to `Context<Decimal64>`, which
  provide inexact conversions from `i64` and `u64`, respectively, to
  `Decimal64`.

* Add the `from_i128` and `from_u128` methods to `Context<Decimal128>`, which
  provide inexact conversions from `i128` and `u128`, respectively, to
  `Decimal128`.

## 0.2.0 - 2021-02-03

* Add the `OrderedDecimal` wrapper type which imbues `Decimal64` and
  `Decimal128` with implementations of `Ord` and `Hash`, akin to
  `ordered_float::OrderedFloat`. The order used is that of the underlying type's
  `partial_cmp`, except that NaNs are considered equal to themselves and sort
  greater than all other values.

* Remove the `Ord` and `Eq` implementations from `Decimal64` and `Decimal128`,
  which used `total_cmp`'s order.

* Change the `PartialCmp` and `PartialEq` implementations of `Decimal64` and
  `Decimal128` to use the semantics of `Context::<D>::partial_cmp` rather than
  `D::total_cmp`. This is analogous to the behavior of the primitive `f32` and
  `f64` types.

* Add associated constants for zero, one, and NaN to each floating-point decimal
  type. The full list of added constants is:

  * `Decimal32::ZERO`
  * `Decimal32::ONE`
  * `Decimal32::NAN`
  * `Decimal64::ZERO`
  * `Decimal64::ONE`
  * `Decimal64::NAN`
  * `Decimal128::ZERO`
  * `Decimal128::ONE`
  * `Decimal128::NAN`

* Remove the `Decimal32::zero`, `Decimal64::zero`, and `Decimal128::zero`
  methods. Use either the `ZERO` associated constant or the `Default`
  implementation instead.

* Mark `Decimal32::from_ne_bytes`, `Decimal64::from_ne_bytes`, and
  `Decimal128::from_ne_bytes` as `const fn`s.

* Add `std::iter::Sum` and `std::iter::Product` implementations for `Decimal64`
  and `Decimal128`.

## 0.1.2 - 2021-02-01

* Correct documentation links in README, again.

## 0.1.1 - 2021-02-01

* Correct documentation links in README.
* Implement `Hash` for the `Class`, `Rounding` and `Status` types.
* Include fields in `fmt::Debug` output for `Status`.

## 0.1.0 - 2021-01-31

Initial release.

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html

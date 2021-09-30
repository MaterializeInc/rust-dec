# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog], and this crate adheres to [Semantic
Versioning].

## Unreleased

* Add `round_to_place` and `reduce_to_place` to `Decimal<N>`, which provide
  "places from the left" rounding, akin to a shift right, round, and shift
  left. `reduce_to_place` performs the operation, as expected, and
  simultaneously performs a `reduce`.

## 0.4.5 - 2021-07-29

* Change `Decimal`'s API for `TryFrom<Decimal<N>> for T` where `T` are primitive
  integers. Previously, these conversions failed when the decimal's exponent was
  not 0. The API now accepts any values without significant digits in the
  value's fractional component, e.g. `1E10`, `2.00`, assuming the values fit
  into the target type.

  To re-implement the prior behavior, check the value's exponent before
  performing the cast and return an error, e.g.

  ```rust
  pub fn cast_requiring_zero_exp<T, const N: usize>(
      d: Decimal<N>,
  ) -> Result<T, dec::error::TryFromDecimalError>
  where
      T: TryFrom<Decimal<N>, Error = dec::error::TryFromDecimalError>,
  {
      if d.exponent() != 0 {
          return Err(dec::error::TryFromDecimalError);
      }
      T::try_from(d)
  }
  ```

## 0.4.4 - 2021-06-25

* Fix a bug that prevented compilation in 32-bit environments.

## 0.4.3 - 2021-06-18

* Genericize precision parameter for `Decimal` functions that take multiple
  arguments, allowing `Decimal` values of different precisions to be used in
  in the same operation.

* Implement the following `std::ops` for `Decimal`:
  - `Add`
  - `AddAssign`
  - `Div`
  - `DivAssign`
  - `Mul`
  - `MulAssign`
  - `Neg`
  - `Rem`
  - `RemAssign`
  - `Sub`
  - `SubAssign`

* Implement remaining traits and functions for casting primitive integers to
  `Decimal` values. These are only quality-of-life improvements and do not
  provide any new functionality.

* Make `Decimal::coefficient_units` public.

## 0.4.2 - 2021-06-04

* Refactor `to_raw_parts` and `to_raw_parts` to use `&[u8]` to represent a
  `Decimal`'s `lsu`.

* Provide `Decimal::digits_to_lsu_elements_len` to provide a mechanism to
  calculate the number of elements `lsu`s should have as a function of their
  digits.

* Remove the `lsu` function, which duplicated `coefficient_unit`'s
  functionality.

## 0.4.1 - 2021-06-03

* Support the following `Decimal` functions:
  - `round`
  - `trim`
  - `from_raw_parts`

* Implement `TryInto<Decimal<N>>` for `f32` and `f64`.

* Implement `From<f32>` and `From<f64>` for `<Decimal<N>>`.

* Change `to_raw_parts` to only return valid digits from a `Decimal`'s `lsu`; it
  previously returned the entire `lsu`, including digits that were no longer
  valid after e.g. `trim` operations.

## 0.4.0 - 2021-05-20

* Add the following methods:

  - `Decimal::infinity`
  - `Decimal::nan`
  - `Decimal::rescale`
  - `Decimal::to_standard_notation_string`
  - `Decimal::set_exponent`
  - `Decimal::to_width` to support casting between different widths of `Decimal`.
  - `Decimal::coefficient<T>...where T: TryFrom<Decimal<N>>` to return
    `Decimal`'s coefficients as arbitrary primitive integers.
  - `Context::<Decimal<N>>::sum`
  - `Context::<Decimal<N>>::product`
  - `Context::set_status`

* Implement `TryInto<Decimal<N>>` for all primitive integers.

* Implement `From<u32>`, `From<u64>`, `From<i32>`, `From<i64>`, `From<usize>`,
  `From<isize>`, `PartialOrd` and `PartialEq` for `Decimal`.

* Support negating `Decimal` values.

* Derive the `Copy` trait for `Decimal`.

* Remove the `arbitrary-precision` feature. The arbitrary-precision `Decimal`
  type is now always compiled.

* Enable using `OrderedDecimal` with the `Decimal` type.

* Implement `BitAnd`, `BitAndAssign`, `BitOr`, and `BitOrAssign` for `Status`.

* Implement `serde::Serialize` and `serde::Deserialize` for `Decimal` when the
  `serde` feature is activated.

* Fix a bug that caused all `to_standard_notation_string` implementations to
  hang on non-finite values, e.g. `NaN`.

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

// Copyright Materialize, Inc. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE file at the
// root of this repository, or online at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! dec is a decimal arithmetic library for Rust.
//!
//! # Introduction
//!
//! From the [Decimal Arithmetic FAQ][faq]:
//!
//! > Most people in the world use decimal (base 10) arithmetic. When large or
//! > small values are needed, exponents which are powers of ten are used.
//! > However, most computers have only binary (base two) arithmetic, and when
//! > exponents are used (in floating-poing numbers) they are powers of two.
//! >
//! > Binary floating-point numbers can only approximate common decimal numbers.
//! > The value 0.1, for example, would need an infinitely recurring binary
//! > fraction. In contrast, a decimal number system can represent 0.1 exactly,
//! > as one tenth (that is, 10<sup>-1</sup>). Consequently, binary
//! > floating-point cannot be used for financial calculations, or indeed for
//! > any calculations where the results achieved are required to match those
//! > which might be calculated by hand.
//!
//! dec is an implementation of the General Decimal Arithmetic standard, which
//! precisely describes both a limited-precision floating-point decimal
//! arithmetic and an arbitrary precision floating-point decimal arithmetic.
//!
//! The latest draft of the standard is available online at
//! <http://speleotrove.com/decimal/decarith.html>. The floating-point
//! arithmetic additionally conforms to the IEEE 754-2008 specification, but
//! this specification is not freely available.
//!
//! # Details
//!
//! dec is a safe Rust API atop the C reference implementation, [libdecnumber].
//! Unsafe C bindings to libdecnumber are available in the [decnumber-sys]
//! crate.
//!
//! The main types exposed by this library are as follows:
//!
//!  * [`Decimal32`], a 32-bit decimal floating-point representation which
//!    provides 7 decimal digits of precision in a compressed format. This type
//!    is intended for storage and interchange only and so does not support any
//!    arithmetic functions.
//!
//!  * [`Decimal64`], a 64-bit decimal floating-point representation which
//!    provides 16 decimal digits of precision in a compressed format along with
//!    various arithmetic functions.
//!
//!  * [`Decimal128`], a 128-bit decimal floating-point representation which
//!    provides 34 decimal digits of precision in a compressed format along with
//!    various arithmetic functions.
//!
//!  * [`Decimal`], a decimal representation whose precision is configurable via
//!    its generic `N` parameter.
//!
//!  * [`Context`], which hosts most of the actual functions on the above types.
//!    A context configures the behavior of the various operations (e.g.,
//!    rounding mode) and accumulates exceptional conditions (e.g., overflow).
//!
//! # Examples
//!
//! The following example demonstrates the basic usage of the library:
//!
//! ```
//! # use std::error::Error;
//! use dec::Decimal128;
//!
//! let x: Decimal128 = ".1".parse()?;
//! let y: Decimal128 = ".2".parse()?;
//! let z: Decimal128 = ".3".parse()?;
//!
//! assert_eq!(x + y, z);
//! assert_eq!((x + y + z).to_string(), "0.6");
//!
//! # Ok::<_, Box<dyn Error>>(())
//! ```
//!
//! [faq]: http://speleotrove.com/decimal/decifaq.html
//! [libdecnumber]: http://speleotrove.com/decimal/decarith.html
//! [decnumber-sys]: https://docs.rs/decnumber-sys

#![deny(missing_debug_implementations, missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]

mod context;
#[macro_use]
mod conv;
mod decimal;
mod decimal128;
mod decimal32;
mod decimal64;
mod error;
mod ordered;
#[cfg(tests)]
mod tests;

pub use context::{Class, Context, Rounding, Status};
pub use decimal::Decimal;
pub use decimal128::Decimal128;
pub use decimal32::Decimal32;
pub use decimal64::Decimal64;
pub use error::{
    InvalidExponentError, InvalidPrecisionError, ParseDecimalError, TryFromDecimalError,
};
pub use ordered::OrderedDecimal;

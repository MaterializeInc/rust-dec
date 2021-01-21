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

use std::fmt;
use std::marker::PhantomData;

use libc::c_uint;

/// A context for performing decimal operations.
///
/// Contexts serve two purposes:
///
///   * They configure various properties of decimal arithmetic, like the
///     rounding algorithm to use.
///
///   * They accumulate any informational and exceptional conditions raised by
///     decimal operations. Multiple operations can be performed on a context
///     and the status need only be checked once at the end. This can improve
///     performance when performing many decimal operations.
///
/// A given context is only valid for use with one decimal type, specified by
/// the `D` type parameter.
///
/// Not all context types support all operations. For example, only the
/// context for the arbitrary-precision decimal type `Decimal` supports
/// configuring precision.
#[derive(Clone)]
pub struct Context<D> {
    pub(crate) inner: decnumber_sys::decContext,
    pub(crate) _phantom: PhantomData<D>,
}

impl<D> fmt::Debug for Context<D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Context")
            .field("clamp", &self.inner.clamp)
            .field("digits", &self.inner.digits)
            .field("emax", &self.inner.emax)
            .field("emin", &self.inner.emin)
            .field("rounding", &self.rounding())
            .field("traps", &self.inner.traps)
            .finish()
    }
}

impl<D> Context<D> {
    /// Returns the context's rounding algorithm.
    pub fn rounding(&self) -> Rounding {
        Rounding::from_c(self.inner.round)
    }

    /// Set's the context's rounding algorithm.
    pub fn set_rounding(&mut self, rounding: Rounding) {
        self.inner.round = rounding.to_c();
    }

    /// Returns the context's status.
    pub fn status(&self) -> Status {
        Status {
            inner: self.inner.status,
        }
    }

    /// Clears the context's status.
    pub fn clear_status(&mut self) {
        self.inner.status = 0;
    }
}

/// Algorithms for rounding decimal numbers.
///
/// The rounding modes are precisely defined in [The Arithmetic Model][model]
/// chapter of the General Decimal Arithmetic specification.
///
/// [model]: http://speleotrove.com/decimal/damodel.html
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Rounding {
    /// Round towards positive infinity.
    Ceiling,
    /// Round towards zero (truncation).
    Down,
    /// Round towards negative infinity.
    Floor,
    /// Round to nearest; if equidistant, round down.
    HalfDown,
    /// Round to nearest; if equidistant, round so that the final digit is even.
    HalfEven,
    /// Round to nearest; if equidistant, round up.
    HalfUp,
    /// Round away from zero.
    Up,
    /// The same as [`Rounding::Up`], except that rounding up only occurs
    /// if the digit to be rounded up is 0 or 5.
    ///
    /// After overflow the result is the same as for [`Rounding::Down`].
    ZeroFiveUp,
}

impl Default for Rounding {
    fn default() -> Rounding {
        Rounding::HalfEven
    }
}

impl Rounding {
    fn from_c(c: c_uint) -> Rounding {
        match c {
            decnumber_sys::DEC_ROUND_CEILING => Rounding::Ceiling,
            decnumber_sys::DEC_ROUND_DOWN => Rounding::Down,
            decnumber_sys::DEC_ROUND_FLOOR => Rounding::Floor,
            decnumber_sys::DEC_ROUND_HALF_DOWN => Rounding::HalfDown,
            decnumber_sys::DEC_ROUND_HALF_EVEN => Rounding::HalfEven,
            decnumber_sys::DEC_ROUND_HALF_UP => Rounding::HalfUp,
            decnumber_sys::DEC_ROUND_UP => Rounding::Up,
            decnumber_sys::DEC_ROUND_05UP => Rounding::ZeroFiveUp,
            _ => unreachable!("invalid C rounding value"),
        }
    }

    fn to_c(&self) -> c_uint {
        match self {
            Rounding::Ceiling => decnumber_sys::DEC_ROUND_CEILING,
            Rounding::Down => decnumber_sys::DEC_ROUND_DOWN,
            Rounding::Floor => decnumber_sys::DEC_ROUND_FLOOR,
            Rounding::HalfDown => decnumber_sys::DEC_ROUND_HALF_DOWN,
            Rounding::HalfEven => decnumber_sys::DEC_ROUND_HALF_EVEN,
            Rounding::HalfUp => decnumber_sys::DEC_ROUND_HALF_UP,
            Rounding::Up => decnumber_sys::DEC_ROUND_UP,
            Rounding::ZeroFiveUp => decnumber_sys::DEC_ROUND_05UP,
        }
    }
}

/// Represents exceptional conditions resulting from operations on decimal
/// numbers.
///
/// For details about the various exceptional conditions, consult the
/// [Exceptional Conditions][conditions] chapter of the General Decimal
/// Arithmetic specification.
///
/// [conditions]: http://speleotrove.com/decimal/daexcep.html
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Status {
    inner: u32,
}

impl Status {
    /// Reports whether any of the condition flags are set.
    pub fn any(&self) -> bool {
        self.inner != 0
    }

    /// Reports whether the conversion syntax flag is set.
    ///
    /// Operations set this flag when an invalid string is converted to a
    /// decimal.
    pub fn conversion_syntax(&self) -> bool {
        self.inner & decnumber_sys::DEC_Conversion_syntax != 0
    }

    /// Reports whether the division by zero flag is set.
    ///
    /// Operations set this flag when a nonzero dividend is divided by zero.
    pub fn division_by_zero(&self) -> bool {
        self.inner & decnumber_sys::DEC_Division_by_zero != 0
    }

    /// Reports whether the division impossible flag is set.
    ///
    /// Operations set this flag if the integer result of a division had too
    /// many digits.
    pub fn division_impossible(&self) -> bool {
        self.inner & decnumber_sys::DEC_Division_impossible != 0
    }

    /// Reports whether the division undefined flag is set.
    ///
    /// Operations set this flag when a zero dividend is divided by zero.
    pub fn division_undefined(&self) -> bool {
        self.inner & decnumber_sys::DEC_Division_undefined != 0
    }

    /// Reports whether the insufficient storage flag is set.
    ///
    /// Operations set this flag if memory allocation fails.
    pub fn insufficient_storage(&self) -> bool {
        self.inner & decnumber_sys::DEC_Insufficient_storage != 0
    }

    /// Reports whether the inexact flag is set.
    ///
    /// Operations set this flag when one or more nonzero coefficient digits
    /// were discarded during rounding from a result.
    pub fn inexact(&self) -> bool {
        self.inner & decnumber_sys::DEC_Inexact != 0
    }

    /// Reports whether the invalid context flag is set.
    ///
    /// Operations set this flag if they detect an invalid context.
    ///
    /// It should not be possible to pass an invalid context to an operation
    /// using this crate, but this method is nonetheless provided for
    /// completeness.
    pub fn invalid_context(&self) -> bool {
        self.inner & decnumber_sys::DEC_Invalid_context != 0
    }

    /// Reports whether the invalid operation flag is set.
    ///
    /// Various operations set this flag in response to invalid arguments.
    pub fn invalid_operation(&self) -> bool {
        self.inner & decnumber_sys::DEC_Invalid_operation != 0
    }

    /// Reports whether the overflow flag is set.
    ///
    /// Operations set this flag when the exponent of a result is too large to
    /// be represented.
    pub fn overflow(&self) -> bool {
        self.inner & decnumber_sys::DEC_Overflow != 0
    }

    /// Reports whether the clamped flag is set.
    ///
    /// Operations set this flag when the exponent of a result has been altered
    /// or constrained in order to fit the constraints of a specific concrete
    /// representation.
    pub fn clamped(&self) -> bool {
        self.inner & decnumber_sys::DEC_Clamped != 0
    }

    /// Reports whether the rounded flag is set.
    ///
    /// Operations set this flag when one or more zero or nonzero coefficient
    /// digits were discarded from a result.
    pub fn rounded(&self) -> bool {
        self.inner & decnumber_sys::DEC_Rounded != 0
    }

    /// Reports whether the subnormal flag is set.
    ///
    /// Operations set this flag when a result's adjusted exponent is less than
    /// E<sub>min</sub> before any rounding.
    pub fn subnormal(&self) -> bool {
        self.inner & decnumber_sys::DEC_Subnormal != 0
    }

    /// Reports whether the underflow flag is set.
    ///
    /// Operations set this flag when a result is both subnormal and inexact.
    pub fn underflow(&self) -> bool {
        self.inner & decnumber_sys::DEC_Underflow != 0
    }
}

/// The class of a decimal number.
///
/// These classes are precisely defined in [The Arithmetic Model][model] chapter
/// of the General Decimal Arithmetic specification.
///
/// [model]: http://speleotrove.com/decimal/damodel.html
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Class {
    /// Signaling NaN ("Not a Number").
    SignalingNan,
    /// Quiet NaN ("Not a Number").
    QuietNan,
    /// Negative infinity.
    NegInfinity,
    /// Negative normal.
    NegNormal,
    /// Negative subnormal.
    NegSubnormal,
    /// Negative zero.
    NegZero,
    /// Positive zero.
    PosZero,
    /// Positive subnormal.
    PosSubnormal,
    /// Positive normal.
    PosNormal,
    /// Positive infinity.
    PosInfinity,
}

impl Class {
    pub(crate) fn from_c(c: c_uint) -> Class {
        match c {
            decnumber_sys::DEC_CLASS_SNAN => Class::SignalingNan,
            decnumber_sys::DEC_CLASS_QNAN => Class::QuietNan,
            decnumber_sys::DEC_CLASS_NEG_INF => Class::NegInfinity,
            decnumber_sys::DEC_CLASS_NEG_NORMAL => Class::NegNormal,
            decnumber_sys::DEC_CLASS_NEG_SUBNORMAL => Class::NegSubnormal,
            decnumber_sys::DEC_CLASS_NEG_ZERO => Class::NegZero,
            decnumber_sys::DEC_CLASS_POS_ZERO => Class::PosZero,
            decnumber_sys::DEC_CLASS_POS_SUBNORMAL => Class::PosSubnormal,
            decnumber_sys::DEC_CLASS_POS_NORMAL => Class::PosNormal,
            decnumber_sys::DEC_CLASS_POS_INF => Class::PosInfinity,
            _ => unreachable!("invalid C class value"),
        }
    }
}

impl fmt::Display for Class {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Class::SignalingNan => f.write_str("sNaN"),
            Class::QuietNan => f.write_str("NaN"),
            Class::NegInfinity => f.write_str("-Infinity"),
            Class::NegNormal => f.write_str("-Normal"),
            Class::NegSubnormal => f.write_str("-Subnormal"),
            Class::NegZero => f.write_str("-Zero"),
            Class::PosZero => f.write_str("+Zero"),
            Class::PosSubnormal => f.write_str("+Subnormal"),
            Class::PosNormal => f.write_str("+Normal"),
            Class::PosInfinity => f.write_str("+Infinity"),
        }
    }
}

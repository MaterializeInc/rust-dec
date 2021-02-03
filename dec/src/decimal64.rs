// Copyright Materialize, Inc. All rights reserved.
//
// Licensed under the Apache License, Version 2.inner (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License in the LICENSE file at the
// root of this repository, or online at
//
//     http://www.apache.org/licenses/LICENSE-2.inner
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::cmp::Ordering;
use std::ffi::{CStr, CString};
use std::fmt;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};
use std::str::FromStr;

use libc::c_char;

use crate::context::{Class, Context};
#[cfg(feature = "arbitrary-precision")]
use crate::decimal::Decimal;
use crate::decimal128::Decimal128;
use crate::decimal32::Decimal32;
use crate::error::ParseDecimalError;

/// A 64-bit decimal floating-point number.
///
/// Additional operations are defined as methods on the [`Context`] type.
///
/// For convenience, `Decimal64` overloads many of the standard Rust operators.
/// For example, you can use the standard `+` operator to add two values
/// together:
///
/// ```
/// use dec::Decimal64;
/// let a = Decimal64::from(1);
/// let b = Decimal64::from(2);
/// assert_eq!(a + b, Decimal64::from(3));
/// ```
///
/// These overloaded operators implicitly construct a single-use default
/// context, which has some performance overhead. For maximum performance when
/// performing operations in bulk, use a long-lived context that you construct
/// yourself.
#[derive(Clone, Copy)]
pub struct Decimal64 {
    pub(crate) inner: decnumber_sys::decDouble,
}

impl Decimal64 {
    /// The value that represents Not-a-Number (NaN).
    pub const NAN: Decimal64 = Decimal64::from_ne_bytes(if cfg!(target_endian = "little") {
        [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x7c]
    } else {
        [0x7c, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
    });

    /// The value that represents zero.
    pub const ZERO: Decimal64 = Decimal64::from_ne_bytes(if cfg!(target_endian = "little") {
        [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x38, 0x22]
    } else {
        [0x22, 0x38, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
    });

    /// Creates a number from its representation as a little-endian byte array.
    pub fn from_le_bytes(mut bytes: [u8; 8]) -> Decimal64 {
        if cfg!(target_endian = "big") {
            bytes.reverse();
        }
        Decimal64::from_ne_bytes(bytes)
    }

    /// Creates a number from its representation as a big-endian byte array.
    pub fn from_be_bytes(mut bytes: [u8; 8]) -> Decimal64 {
        if cfg!(target_endian = "little") {
            bytes.reverse();
        }
        Decimal64::from_ne_bytes(bytes)
    }

    /// Creates a number from its representation as a byte array in the
    /// native endianness of the target platform.
    pub const fn from_ne_bytes(bytes: [u8; 8]) -> Decimal64 {
        Decimal64 {
            inner: decnumber_sys::decDouble { bytes },
        }
    }

    /// Returns the memory representation of the number as a byte array in
    /// little-endian order.
    pub fn to_le_bytes(&self) -> [u8; 8] {
        let mut bytes = self.to_ne_bytes();
        if cfg!(target_endian = "big") {
            bytes.reverse();
        }
        bytes
    }

    /// Returns the memory representation of the number as a byte array in
    /// big-endian order.
    pub fn to_be_bytes(&self) -> [u8; 8] {
        let mut bytes = self.to_ne_bytes();
        if cfg!(target_endian = "little") {
            bytes.reverse();
        }
        bytes
    }

    /// Returns the memory representation of the number as a byte array in
    /// the native endianness of the target platform.
    pub fn to_ne_bytes(&self) -> [u8; 8] {
        self.inner.bytes
    }

    /// Classifies the number.
    pub fn class(&self) -> Class {
        Class::from_c(unsafe { decnumber_sys::decDoubleClass(&self.inner) })
    }

    /// Computes the number of significant digits in the number.
    ///
    /// If the number is zero or infinite, returns 1. If the number is a NaN,
    /// returns the number of digits in the payload.
    pub fn digits(&self) -> u32 {
        unsafe { decnumber_sys::decDoubleDigits(&self.inner) }
    }

    /// Computes the exponent of the number.
    pub fn exponent(&self) -> i32 {
        unsafe { decnumber_sys::decDoubleGetExponent(&self.inner) }
    }

    /// Returns an equivalent number whose encoding is guaranteed to be
    /// canonical.
    pub fn canonical(mut self) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleCanonical(&mut self.inner, &self.inner);
        }
        self
    }

    /// Reports whether the encoding of the number is canonical.
    pub fn is_canonical(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsCanonical(&self.inner) != 0 }
    }

    /// Reports whether the number is finite.
    ///
    /// A finite number is one that is neither infinite nor a NaN.
    pub fn is_finite(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsFinite(&self.inner) != 0 }
    }

    /// Reports whether the number is positive or negative infinity.
    pub fn is_infinite(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsInfinite(&self.inner) != 0 }
    }

    /// Reports whether the number is an integer.
    ///
    /// An integer is a decimal number that is finite and has an exponent of
    /// zero.
    pub fn is_integer(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsInteger(&self.inner) != 0 }
    }

    /// Reports whether the number is a valid argument for logical operations.
    ///
    /// A number is a valid argument for logical operations if it is a
    /// nonnegative integer where each digit is either zero or one.
    pub fn is_logical(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsInteger(&self.inner) != 0 }
    }

    /// Reports whether the number is a NaN.
    pub fn is_nan(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsNaN(&self.inner) != 0 }
    }

    /// Reports whether the number is less than zero and not a NaN.
    pub fn is_negative(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsNegative(&self.inner) != 0 }
    }

    /// Reports whether the number is normal.
    ///
    /// A normal number is finite, non-zero, and not subnormal.
    pub fn is_normal(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsNormal(&self.inner) != 0 }
    }

    /// Reports whether the number is greater than zero and not a NaN.
    pub fn is_positive(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsPositive(&self.inner) != 0 }
    }

    /// Reports whether the number is a signaling NaN.
    pub fn is_signaling_nan(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsSignaling(&self.inner) != 0 }
    }

    /// Reports whether the number has a sign of 1.
    ///
    /// Note that zeros and NaNs may have a sign of 1.
    pub fn is_signed(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsSigned(&self.inner) != 0 }
    }

    /// Reports whether the number is subnormal.
    ///
    /// A subnormal number is finite, non-zero, and has magnitude less than
    /// 10<sup>emin</sup>.
    pub fn is_subnormal(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsSubnormal(&self.inner) != 0 }
    }

    /// Reports whether the number is positive or negative zero.
    pub fn is_zero(&self) -> bool {
        unsafe { decnumber_sys::decDoubleIsZero(&self.inner) != 0 }
    }

    /// Reports whether the quantum of the number matches the quantum of
    /// `rhs`.
    ///
    /// Quantums are considered to match if the numbers have the same exponent,
    /// are both NaNs, or both infinite.
    pub fn quantum_matches(&self, rhs: &Decimal64) -> bool {
        unsafe { decnumber_sys::decDoubleSameQuantum(&self.inner, &rhs.inner) != 0 }
    }

    /// Determines the ordering of this number relative to `rhs`, using the
    /// total order predicate defined in IEEE 754-2008.
    ///
    /// For a brief description of the ordering, consult [`f32::total_cmp`].
    pub fn total_cmp(&self, rhs: &Decimal64) -> Ordering {
        let mut d = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d = Decimal64 {
            inner: unsafe {
                decnumber_sys::decDoubleCompareTotal(d.as_mut_ptr(), &self.inner, &rhs.inner);
                d.assume_init()
            },
        };
        if d.is_positive() {
            Ordering::Greater
        } else if d.is_negative() {
            Ordering::Less
        } else {
            debug_assert!(d.is_zero());
            Ordering::Equal
        }
    }
}

impl Default for Decimal64 {
    fn default() -> Decimal64 {
        Decimal64::ZERO
    }
}

impl fmt::Debug for Decimal64 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Decimal64 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = MaybeUninit::<[c_char; decnumber_sys::DECDOUBLE_String]>::uninit();
        let c_str = unsafe {
            if f.alternate() {
                decnumber_sys::decDoubleToEngString(&self.inner, buf.as_mut_ptr() as *mut c_char);
            } else {
                decnumber_sys::decDoubleToString(&self.inner, buf.as_mut_ptr() as *mut c_char);
            }
            CStr::from_ptr(buf.as_ptr() as *const c_char)
        };
        f.write_str(
            c_str
                .to_str()
                .expect("decDoubleToString yields valid UTF-8"),
        )
    }
}

impl FromStr for Decimal64 {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Decimal64, ParseDecimalError> {
        Context::<Decimal64>::default().parse(s)
    }
}

impl From<i32> for Decimal64 {
    fn from(n: i32) -> Decimal64 {
        let mut d = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d = unsafe {
            decnumber_sys::decDoubleFromInt32(d.as_mut_ptr(), n);
            d.assume_init()
        };
        Decimal64 { inner: d }
    }
}

impl From<u32> for Decimal64 {
    fn from(n: u32) -> Decimal64 {
        let mut d = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d = unsafe {
            decnumber_sys::decDoubleFromUInt32(d.as_mut_ptr(), n);
            d.assume_init()
        };
        Decimal64 { inner: d }
    }
}

impl From<Decimal32> for Decimal64 {
    fn from(d32: Decimal32) -> Decimal64 {
        let mut d64 = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d64 = unsafe {
            decnumber_sys::decSingleToWider(&d32.inner, d64.as_mut_ptr());
            d64.assume_init()
        };
        Decimal64 { inner: d64 }
    }
}

impl PartialOrd for Decimal64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Context::<Decimal64>::default().partial_cmp(*self, *other)
    }
}

impl PartialEq for Decimal64 {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl Add<Decimal64> for Decimal64 {
    type Output = Decimal64;

    fn add(self, rhs: Decimal64) -> Decimal64 {
        Context::<Decimal64>::default().add(self, rhs)
    }
}

impl AddAssign<Decimal64> for Decimal64 {
    fn add_assign(&mut self, rhs: Decimal64) {
        *self = Context::<Decimal64>::default().add(*self, rhs);
    }
}

impl Div<Decimal64> for Decimal64 {
    type Output = Decimal64;

    fn div(self, rhs: Decimal64) -> Decimal64 {
        Context::<Decimal64>::default().div(self, rhs)
    }
}

impl DivAssign<Decimal64> for Decimal64 {
    fn div_assign(&mut self, rhs: Decimal64) {
        *self = Context::<Decimal64>::default().div(*self, rhs);
    }
}

impl Mul<Decimal64> for Decimal64 {
    type Output = Decimal64;

    fn mul(self, rhs: Decimal64) -> Decimal64 {
        Context::<Decimal64>::default().mul(self, rhs)
    }
}

impl MulAssign<Decimal64> for Decimal64 {
    fn mul_assign(&mut self, rhs: Decimal64) {
        *self = Context::<Decimal64>::default().mul(*self, rhs);
    }
}

impl Rem<Decimal64> for Decimal64 {
    type Output = Decimal64;

    fn rem(self, rhs: Decimal64) -> Decimal64 {
        Context::<Decimal64>::default().rem(self, rhs)
    }
}

impl RemAssign<Decimal64> for Decimal64 {
    fn rem_assign(&mut self, rhs: Decimal64) {
        *self = Context::<Decimal64>::default().rem(*self, rhs);
    }
}

impl Sub<Decimal64> for Decimal64 {
    type Output = Decimal64;

    fn sub(self, rhs: Decimal64) -> Decimal64 {
        Context::<Decimal64>::default().sub(self, rhs)
    }
}

impl SubAssign<Decimal64> for Decimal64 {
    fn sub_assign(&mut self, rhs: Decimal64) {
        *self = Context::<Decimal64>::default().sub(*self, rhs);
    }
}

impl Default for Context<Decimal64> {
    fn default() -> Context<Decimal64> {
        let mut ctx = MaybeUninit::<decnumber_sys::decContext>::uninit();
        let ctx = unsafe {
            decnumber_sys::decContextDefault(ctx.as_mut_ptr(), decnumber_sys::DEC_INIT_DECDOUBLE);
            ctx.assume_init()
        };
        Context {
            inner: ctx,
            _phantom: PhantomData,
        }
    }
}

impl Context<Decimal64> {
    /// Parses a number from its string representation.
    pub fn parse<S>(&mut self, s: S) -> Result<Decimal64, ParseDecimalError>
    where
        S: Into<Vec<u8>>,
    {
        let c_string = CString::new(s).map_err(|_| ParseDecimalError)?;
        let mut d = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d = unsafe {
            decnumber_sys::decDoubleFromString(d.as_mut_ptr(), c_string.as_ptr(), &mut self.inner);
            d.assume_init()
        };
        if (self.inner.status & decnumber_sys::DEC_Conversion_syntax) != 0 {
            Err(ParseDecimalError)
        } else {
            Ok(Decimal64 { inner: d })
        }
    }

    /// Constructs a number from a 128-bit decimal float.
    ///
    /// The result may be inexact. The status fields on the context will be set
    /// appropriately if so.
    pub fn from_decimal128(&mut self, d128: Decimal128) -> Decimal64 {
        let mut d64 = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d64 = unsafe {
            decnumber_sys::decDoubleFromWider(d64.as_mut_ptr(), &d128.inner, &mut self.inner);
            d64.assume_init()
        };
        Decimal64 { inner: d64 }
    }

    /// Constructs a number from an arbitrary-precision decimal.
    ///
    /// The result may be inexact. The status fields on the context will be set
    /// appropriately if so.
    #[cfg(feature = "arbitrary-precision")]
    pub fn from_decimal<const N: usize>(&mut self, d: &Decimal<N>) -> Decimal64 {
        let mut d64 = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d64 = unsafe {
            decnumber_sys::decimal64FromNumber(d64.as_mut_ptr(), d.as_ptr(), &mut self.inner);
            d64.assume_init()
        };
        Decimal64 { inner: d64 }
    }

    /// Computes the absolute value of `n`.
    ///
    /// This has the same effect as [`Context::<Decimal64>::plus`] unless
    /// `n` is negative, in which case it has the same effect as
    /// [`Context::<Decimal64>::minus`].
    ///
    /// The returned result will be canonical.
    pub fn abs(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleAbs(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Adds `lhs` and `rhs`.
    pub fn add(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleAdd(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Carries out the digitwise logical and of `lhs` and `rhs`.
    ///
    /// The operands must be valid for logical operations.
    /// See [`Decimal64::is_logical`].
    pub fn and(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleAnd(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Divides `lhs` by `rhs`.
    pub fn div(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleDivide(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Divides `lhs` by `rhs` and returns the integer part of the result
    /// (rounded towards zero) with an exponent of 0.
    ///
    /// If the result would overflow, then [`Status::division_impossible`] is
    /// set.
    ///
    /// [`Status::division_impossible`]: crate::context::Status::division_impossible
    pub fn div_integer(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleDivideInteger(
                &mut lhs.inner,
                &lhs.inner,
                &rhs.inner,
                &mut self.inner,
            );
        }
        lhs
    }

    /// Calculates the fused multiply-add `(x * y) + z`.
    ///
    /// The multiplication is carried out first and is exact, so this operation
    /// only has the one, final rounding.
    pub fn fma(&mut self, mut x: Decimal64, y: Decimal64, z: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleFMA(
                &mut x.inner,
                &x.inner,
                &y.inner,
                &z.inner,
                &mut self.inner,
            );
        }
        x
    }

    /// Carries out the digitwise logical inversion of `n`.
    ///
    /// The operand must be valid for logical operation.
    /// See [`Decimal64::is_logical`].
    pub fn invert(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleInvert(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Computes the adjusted exponent of the number, according to IEEE 754
    /// rules.
    pub fn logb(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleLogB(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Returns whichever of `lhs` and `rhs` is larger.
    ////
    /// The comparison is performed using the same rules as for
    /// [`Decimal64::total_cmp`].
    pub fn max(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleMax(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Returns whichever of `lhs` and `rhs` has the largest absolute value.
    pub fn max_abs(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleMaxMag(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Returns whichever of `lhs` and `rhs` is smaller.
    ////
    /// The comparison is performed using the same rules as for
    /// [`Decimal64::total_cmp`].
    pub fn min(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleMin(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Returns whichever of `lhs` and `rhs` has the largest absolute value.
    pub fn min_abs(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleMinMag(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Subtracts `n` from zero.
    pub fn minus(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleMinus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Divides `lhs` by `rhs`.
    pub fn mul(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleMultiply(
                &mut lhs.inner,
                &lhs.inner,
                &rhs.inner,
                &mut self.inner,
            );
        }
        lhs
    }

    /// Returns the next number to `n` in the direction of negative infinity.
    ///
    /// This operation follows the IEEE 754 rules for the *nextDown* operation.
    pub fn next_minus(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleNextMinus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Returns the next number to `n` in the direction of positive infinity.
    ///
    /// This operation follows the IEEE 754 rules for the *nextUp* operation.
    pub fn next_plus(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleNextPlus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Returns the next number to `x` in the direction of `y`.
    ///
    /// This operation follows the IEEE 754 rules for the *nextAfter* operation.
    pub fn next_toward(&mut self, mut x: Decimal64, y: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleNextToward(&mut x.inner, &x.inner, &y.inner, &mut self.inner);
        }
        x
    }

    /// Determines the ordering of `lhs` relative to `rhs`, using a partial
    /// order.
    ///
    /// If either `lhs` or `rhs` is a NaN, returns `None`. To force an ordering
    /// upon NaNs, use [`Decimal64::total_cmp`] or
    /// [`OrderedDecimal`](crate::OrderedDecimal).
    pub fn partial_cmp(&mut self, lhs: Decimal64, rhs: Decimal64) -> Option<Ordering> {
        let mut d = MaybeUninit::<decnumber_sys::decDouble>::uninit();
        let d = Decimal64 {
            inner: unsafe {
                decnumber_sys::decDoubleCompare(
                    d.as_mut_ptr(),
                    &lhs.inner,
                    &rhs.inner,
                    &mut self.inner,
                );
                d.assume_init()
            },
        };
        if d.is_positive() {
            Some(Ordering::Greater)
        } else if d.is_negative() {
            Some(Ordering::Less)
        } else if d.is_zero() {
            Some(Ordering::Equal)
        } else {
            debug_assert!(d.is_nan());
            None
        }
    }

    /// Adds `n` to zero.
    pub fn plus(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoublePlus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Rounds or pads `lhs` so that it has the same exponent as `rhs`.
    pub fn quantize(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleQuantize(
                &mut lhs.inner,
                &lhs.inner,
                &rhs.inner,
                &mut self.inner,
            );
        }
        lhs
    }

    /// Reduces the number's coefficient to its shortest possible form without
    /// changing the value of the result.
    ///
    /// This removes all possible trailing zeros; some may remain when the
    /// number is very close to the most positive or most negative number.
    pub fn reduce(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleReduce(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Integer-divides `lhs` by `rhs` and returns the remainder from the
    /// division.
    pub fn rem(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleRemainder(
                &mut lhs.inner,
                &lhs.inner,
                &rhs.inner,
                &mut self.inner,
            );
        }
        lhs
    }

    /// Like [`rem`](Context::<Decimal64>::rem), but uses the IEEE 754
    /// rules for remainder operations.
    pub fn rem_near(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleRemainderNear(
                &mut lhs.inner,
                &lhs.inner,
                &rhs.inner,
                &mut self.inner,
            );
        }
        lhs
    }

    /// Rotates the digits of `lhs` by `rhs`.
    ///
    /// If `rhs` is positive, rotates to the left. If `rhs` is negative, rotates
    /// to the right.
    ///
    /// `rhs` specifies the number of positions to rotate, and must be a finite
    /// integer. NaNs are propagated as usual.
    ///
    /// If `lhs` is infinity, the result is infinity of the same sign.
    pub fn rotate(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleRotate(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Rounds the number to an integral value using the rounding mode in the
    /// context.
    pub fn round(&mut self, mut n: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleToIntegralExact(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Multiplies `x` by 10<sup>`y`</sup>.
    pub fn scaleb(&mut self, mut x: Decimal64, y: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleScaleB(&mut x.inner, &x.inner, &y.inner, &mut self.inner);
        }
        x
    }

    /// Shifts the digits of `lhs` by `rhs`.
    ///
    /// If `rhs` is positive, shifts to the left. If `rhs` is negative, shifts
    /// to the right. Any digits "shifted in" will be zero.
    ///
    /// `rhs` specifies the number of positions to shift, and must be a finite
    /// integer. NaNs are propagated as usual.
    ///
    /// If `lhs` is infinity, the result is infinity of the same sign.
    pub fn shift(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleShift(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Subtracts `rhs` from `lhs`.
    pub fn sub(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleSubtract(
                &mut lhs.inner,
                &lhs.inner,
                &rhs.inner,
                &mut self.inner,
            );
        }
        lhs
    }

    /// Carries out the digitwise logical or of `lhs` and `rhs`.
    ///
    /// The operands must be valid for logical operations.
    /// See [`Decimal64::is_logical`].
    pub fn or(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleOr(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Carries out the digitwise logical exclusive or of `lhs` and `rhs`.
    ///
    /// The operands must be valid for logical operations.
    /// See [`Decimal64::is_logical`].
    pub fn xor(&mut self, mut lhs: Decimal64, rhs: Decimal64) -> Decimal64 {
        unsafe {
            decnumber_sys::decDoubleXor(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }
}

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
use crate::decimal32::Decimal32;
use crate::decimal64::Decimal64;
use crate::error::ParseDecimalError;

/// A 128-bit decimal floating-point number.
///
/// Additional operations are defined as methods on the [`Context`] type.
///
/// For convenience, `Decimal128` overloads many of the standard Rust operators.
/// For example, you can use the standard `+` operator to add two values
/// together:
///
/// ```
/// use dec::Decimal128;
/// let a = Decimal128::from(1);
/// let b = Decimal128::from(2);
/// assert_eq!(a + b, Decimal128::from(3));
/// ```
///
/// These overloaded operators implicitly construct a single-use default
/// context, which has some performance overhead. For maximum performance when
/// performing operations in bulk, use a long-lived context that you construct
/// yourself.
#[derive(Clone, Copy)]
pub struct Decimal128 {
    pub(crate) inner: decnumber_sys::decQuad,
}

impl Decimal128 {
    /// Constructs a 128-bit decimal floating-point number representing the
    /// number 0.
    pub fn zero() -> Decimal128 {
        Decimal128::default()
    }

    /// Creates a number from its representation as a little-endian byte array.
    pub fn from_le_bytes(mut bytes: [u8; 16]) -> Decimal128 {
        if cfg!(target_endian = "big") {
            bytes.reverse();
        }
        Decimal128::from_ne_bytes(bytes)
    }

    /// Creates a number from its representation as a big-endian byte array.
    pub fn from_be_bytes(mut bytes: [u8; 16]) -> Decimal128 {
        if cfg!(target_endian = "little") {
            bytes.reverse();
        }
        Decimal128::from_ne_bytes(bytes)
    }

    /// Creates a number from its representation as a byte array in the
    /// native endianness of the target platform.
    pub fn from_ne_bytes(bytes: [u8; 16]) -> Decimal128 {
        Decimal128 {
            inner: decnumber_sys::decQuad { bytes },
        }
    }

    /// Returns the memory representation of the number as a byte array in
    /// little-endian order.
    pub fn to_le_bytes(&self) -> [u8; 16] {
        let mut bytes = self.to_ne_bytes();
        if cfg!(target_endian = "big") {
            bytes.reverse();
        }
        bytes
    }

    /// Returns the memory representation of the number as a byte array in
    /// big-endian order.
    pub fn to_be_bytes(&self) -> [u8; 16] {
        let mut bytes = self.to_ne_bytes();
        if cfg!(target_endian = "little") {
            bytes.reverse();
        }
        bytes
    }

    /// Returns the memory representation of the number as a byte array in
    /// the native endianness of the target platform.
    pub fn to_ne_bytes(&self) -> [u8; 16] {
        self.inner.bytes
    }

    /// Classifies the number.
    pub fn class(&self) -> Class {
        Class::from_c(unsafe { decnumber_sys::decQuadClass(&self.inner) })
    }

    /// Computes the number of significant digits in the number.
    ///
    /// If the number is zero or infinite, returns 1. If the number is a NaN,
    /// returns the number of digits in the payload.
    pub fn digits(&self) -> u32 {
        unsafe { decnumber_sys::decQuadDigits(&self.inner) }
    }

    /// Computes the exponent of the number.
    pub fn exponent(&self) -> i32 {
        unsafe { decnumber_sys::decQuadGetExponent(&self.inner) }
    }

    /// Returns an equivalent number whose encoding is guaranteed to be
    /// canonical.
    pub fn canonical(mut self) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadCanonical(&mut self.inner, &self.inner);
        }
        self
    }

    /// Reports whether the encoding of the number is canonical.
    pub fn is_canonical(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsCanonical(&self.inner) != 0 }
    }

    /// Reports whether the number is finite.
    ///
    /// A finite number is one that is neither infinite nor a NaN.
    pub fn is_finite(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsFinite(&self.inner) != 0 }
    }

    /// Reports whether the number is positive or negative infinity.
    pub fn is_infinite(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsInfinite(&self.inner) != 0 }
    }

    /// Reports whether the number is an integer.
    ///
    /// An integer is a decimal number that is finite and has an exponent of
    /// zero.
    pub fn is_integer(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsInteger(&self.inner) != 0 }
    }

    /// Reports whether the number is a valid argument for logical operations.
    ///
    /// A number is a valid argument for logical operations if it is a
    /// nonnegative integer where each digit is either zero or one.
    pub fn is_logical(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsInteger(&self.inner) != 0 }
    }

    /// Reports whether the number is a NaN.
    pub fn is_nan(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsNaN(&self.inner) != 0 }
    }

    /// Reports whether the number is less than zero and not a NaN.
    pub fn is_negative(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsNegative(&self.inner) != 0 }
    }

    /// Reports whether the number is normal.
    ///
    /// A normal number is finite, non-zero, and not subnormal.
    pub fn is_normal(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsNormal(&self.inner) != 0 }
    }

    /// Reports whether the number is greater than zero and not a NaN.
    pub fn is_positive(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsPositive(&self.inner) != 0 }
    }

    /// Reports whether the number is a signaling NaN.
    pub fn is_signaling_nan(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsSignaling(&self.inner) != 0 }
    }

    /// Reports whether the number has a sign of 1.
    ///
    /// Note that zeros and NaNs may have a sign of 1.
    pub fn is_signed(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsSigned(&self.inner) != 0 }
    }

    /// Reports whether the number is subnormal.
    ///
    /// A subnormal number is finite, non-zero, and has magnitude less than
    /// 10<sup>emin</sup>.
    pub fn is_subnormal(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsSubnormal(&self.inner) != 0 }
    }

    /// Reports whether the number is positive or negative zero.
    pub fn is_zero(&self) -> bool {
        unsafe { decnumber_sys::decQuadIsZero(&self.inner) != 0 }
    }

    /// Reports whether the quantum of the number matches the quantum of
    /// `rhs`.
    ///
    /// Quantums are considered to match if the numbers have the same exponent,
    /// are both NaNs, or both infinite.
    pub fn quantum_matches(&self, rhs: &Decimal128) -> bool {
        unsafe { decnumber_sys::decQuadSameQuantum(&self.inner, &rhs.inner) != 0 }
    }

    /// Determines the ordering of this number relative to `rhs`, using the
    /// total order predicate defined in IEEE 754-2008.
    ///
    /// For a brief description of the ordering, consult [`f32::total_cmp`].
    pub fn total_cmp(&self, rhs: &Decimal128) -> Ordering {
        let mut d = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d = Decimal128 {
            inner: unsafe {
                decnumber_sys::decQuadCompareTotal(d.as_mut_ptr(), &self.inner, &rhs.inner);
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

impl Default for Decimal128 {
    fn default() -> Decimal128 {
        let mut d = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d = unsafe {
            decnumber_sys::decQuadZero(d.as_mut_ptr());
            d.assume_init()
        };
        Decimal128 { inner: d }
    }
}

impl fmt::Debug for Decimal128 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Decimal128 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = MaybeUninit::<[c_char; decnumber_sys::DECQUAD_String]>::uninit();
        let c_str = unsafe {
            if f.alternate() {
                decnumber_sys::decQuadToEngString(&self.inner, buf.as_mut_ptr() as *mut c_char);
            } else {
                decnumber_sys::decQuadToString(&self.inner, buf.as_mut_ptr() as *mut c_char);
            }
            CStr::from_ptr(buf.as_ptr() as *const c_char)
        };
        f.write_str(c_str.to_str().expect("decQuadToString yields valid UTF-8"))
    }
}

impl FromStr for Decimal128 {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Decimal128, ParseDecimalError> {
        Context::<Decimal128>::default().parse(s)
    }
}

impl From<i32> for Decimal128 {
    fn from(n: i32) -> Decimal128 {
        let mut d = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d = unsafe {
            decnumber_sys::decQuadFromInt32(d.as_mut_ptr(), n);
            d.assume_init()
        };
        Decimal128 { inner: d }
    }
}

impl From<u32> for Decimal128 {
    fn from(n: u32) -> Decimal128 {
        let mut d = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d = unsafe {
            decnumber_sys::decQuadFromUInt32(d.as_mut_ptr(), n);
            d.assume_init()
        };
        Decimal128 { inner: d }
    }
}

impl From<Decimal32> for Decimal128 {
    fn from(d32: Decimal32) -> Decimal128 {
        Decimal128::from(Decimal64::from(d32))
    }
}

impl From<Decimal64> for Decimal128 {
    fn from(d64: Decimal64) -> Decimal128 {
        let mut d128 = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d128 = unsafe {
            decnumber_sys::decDoubleToWider(&d64.inner, d128.as_mut_ptr());
            d128.assume_init()
        };
        Decimal128 { inner: d128 }
    }
}

impl PartialEq for Decimal128 {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Decimal128 {}

impl PartialOrd for Decimal128 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Decimal128 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.total_cmp(other)
    }
}

impl Add<Decimal128> for Decimal128 {
    type Output = Decimal128;

    fn add(self, rhs: Decimal128) -> Decimal128 {
        Context::<Decimal128>::default().add(self, rhs)
    }
}

impl AddAssign<Decimal128> for Decimal128 {
    fn add_assign(&mut self, rhs: Decimal128) {
        *self = Context::<Decimal128>::default().add(*self, rhs);
    }
}

impl Div<Decimal128> for Decimal128 {
    type Output = Decimal128;

    fn div(self, rhs: Decimal128) -> Decimal128 {
        Context::<Decimal128>::default().div(self, rhs)
    }
}

impl DivAssign<Decimal128> for Decimal128 {
    fn div_assign(&mut self, rhs: Decimal128) {
        *self = Context::<Decimal128>::default().div(*self, rhs);
    }
}

impl Mul<Decimal128> for Decimal128 {
    type Output = Decimal128;

    fn mul(self, rhs: Decimal128) -> Decimal128 {
        Context::<Decimal128>::default().mul(self, rhs)
    }
}

impl MulAssign<Decimal128> for Decimal128 {
    fn mul_assign(&mut self, rhs: Decimal128) {
        *self = Context::<Decimal128>::default().mul(*self, rhs);
    }
}

impl Rem<Decimal128> for Decimal128 {
    type Output = Decimal128;

    fn rem(self, rhs: Decimal128) -> Decimal128 {
        Context::<Decimal128>::default().rem(self, rhs)
    }
}

impl RemAssign<Decimal128> for Decimal128 {
    fn rem_assign(&mut self, rhs: Decimal128) {
        *self = Context::<Decimal128>::default().rem(*self, rhs);
    }
}

impl Sub<Decimal128> for Decimal128 {
    type Output = Decimal128;

    fn sub(self, rhs: Decimal128) -> Decimal128 {
        Context::<Decimal128>::default().sub(self, rhs)
    }
}

impl SubAssign<Decimal128> for Decimal128 {
    fn sub_assign(&mut self, rhs: Decimal128) {
        *self = Context::<Decimal128>::default().sub(*self, rhs);
    }
}

impl Default for Context<Decimal128> {
    fn default() -> Context<Decimal128> {
        let mut ctx = MaybeUninit::<decnumber_sys::decContext>::uninit();
        let ctx = unsafe {
            decnumber_sys::decContextDefault(ctx.as_mut_ptr(), decnumber_sys::DEC_INIT_DECQUAD);
            ctx.assume_init()
        };
        Context {
            inner: ctx,
            _phantom: PhantomData,
        }
    }
}

impl Context<Decimal128> {
    /// Parses a number from its string representation.
    pub fn parse<S>(&mut self, s: S) -> Result<Decimal128, ParseDecimalError>
    where
        S: Into<Vec<u8>>,
    {
        let c_string = CString::new(s).map_err(|_| ParseDecimalError)?;
        let mut d = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d = unsafe {
            decnumber_sys::decQuadFromString(d.as_mut_ptr(), c_string.as_ptr(), &mut self.inner);
            d.assume_init()
        };
        if (self.inner.status & decnumber_sys::DEC_Conversion_syntax) != 0 {
            Err(ParseDecimalError)
        } else {
            Ok(Decimal128 { inner: d })
        }
    }

    /// Constructs a number from an arbitrary-precision decimal.
    ///
    /// The result may be inexact. The status fields on the context will be set
    /// appropriately if so.
    #[cfg(feature = "arbitrary-precision")]
    pub fn from_decimal<const N: usize>(&mut self, d: &Decimal<N>) -> Decimal128 {
        let mut d128 = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d128 = unsafe {
            decnumber_sys::decimal128FromNumber(d128.as_mut_ptr(), d.as_ptr(), &mut self.inner);
            d128.assume_init()
        };
        Decimal128 { inner: d128 }
    }

    /// Computes the absolute value of `n`.
    ///
    /// This has the same effect as [`Context::<Decimal128>::plus`] unless
    /// `n` is negative, in which case it has the same effect as
    /// [`Context::<Decimal128>::minus`].
    ///
    /// The returned result will be canonical.
    pub fn abs(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadAbs(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Adds `lhs` and `rhs`.
    pub fn add(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadAdd(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Carries out the digitwise logical and of `lhs` and `rhs`.
    ///
    /// The operands must be valid for logical operations.
    /// See [`Decimal128::is_logical`].
    pub fn and(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadAnd(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Divides `lhs` by `rhs`.
    pub fn div(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadDivide(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
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
    pub fn div_integer(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadDivideInteger(
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
    pub fn fma(&mut self, mut x: Decimal128, y: Decimal128, z: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadFMA(&mut x.inner, &x.inner, &y.inner, &z.inner, &mut self.inner);
        }
        x
    }

    /// Carries out the digitwise logical inversion of `n`.
    ///
    /// The operand must be valid for logical operation.
    /// See [`Decimal128::is_logical`].
    pub fn invert(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadInvert(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Computes the adjusted exponent of the number, according to IEEE 754
    /// rules.
    pub fn logb(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadLogB(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Returns whichever of `lhs` and `rhs` is larger.
    ////
    /// The comparison is performed using the same rules as for
    /// [`Decimal128::total_cmp`].
    pub fn max(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadMax(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Returns whichever of `lhs` and `rhs` has the largest absolute value.
    pub fn max_abs(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadMaxMag(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Returns whichever of `lhs` and `rhs` is smaller.
    ////
    /// The comparison is performed using the same rules as for
    /// [`Decimal128::total_cmp`].
    pub fn min(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadMin(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Returns whichever of `lhs` and `rhs` has the largest absolute value.
    pub fn min_abs(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadMinMag(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Subtracts `n` from zero.
    pub fn minus(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadMinus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Divides `lhs` by `rhs`.
    pub fn mul(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadMultiply(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Returns the next number to `n` in the direction of negative infinity.
    ///
    /// This operation follows the IEEE 754 rules for the *nextDown* operation.
    pub fn next_minus(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadNextMinus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Returns the next number to `n` in the direction of positive infinity.
    ///
    /// This operation follows the IEEE 754 rules for the *nextUp* operation.
    pub fn next_plus(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadNextPlus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Returns the next number to `x` in the direction of `y`.
    ///
    /// This operation follows the IEEE 754 rules for the *nextAfter* operation.
    pub fn next_toward(&mut self, mut x: Decimal128, y: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadNextToward(&mut x.inner, &x.inner, &y.inner, &mut self.inner);
        }
        x
    }

    /// Determines the ordering of `lhs` relative to `rhs`, using a partial
    /// order.
    ///
    /// If either `lhs` or `rhs` is a NaN, returns `None`. To force an ordering
    /// upon NaNs, use [`Decimal128::total_cmp`].
    pub fn partial_cmp(&mut self, lhs: Decimal128, rhs: Decimal128) -> Option<Ordering> {
        let mut d = MaybeUninit::<decnumber_sys::decQuad>::uninit();
        let d = Decimal128 {
            inner: unsafe {
                decnumber_sys::decQuadCompare(
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
    pub fn plus(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadPlus(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Rounds or pads `lhs` so that it has the same exponent as `rhs`.
    pub fn quantize(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadQuantize(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Reduces the number's coefficient to its shortest possible form without
    /// changing the value of the result.
    ///
    /// This removes all possible trailing zeros; some may remain when the
    /// number is very close to the most positive or most negative number.
    pub fn reduce(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadReduce(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Integer-divides `lhs` by `rhs` and returns the remainder from the
    /// division.
    pub fn rem(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadRemainder(
                &mut lhs.inner,
                &lhs.inner,
                &rhs.inner,
                &mut self.inner,
            );
        }
        lhs
    }

    /// Like [`rem`](Context::<Decimal128>::rem), but uses the IEEE 754
    /// rules for remainder operations.
    pub fn rem_near(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadRemainderNear(
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
    pub fn rotate(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadRotate(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Rounds the number to an integral value using the rounding mode in
    /// the context.
    pub fn round(&mut self, mut n: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadToIntegralExact(&mut n.inner, &n.inner, &mut self.inner);
        }
        n
    }

    /// Multiplies `x` by 10<sup>`y`</sup>.
    pub fn scaleb(&mut self, mut x: Decimal128, y: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadScaleB(&mut x.inner, &x.inner, &y.inner, &mut self.inner);
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
    pub fn shift(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadShift(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Subtracts `rhs` from `lhs`.
    pub fn sub(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadSubtract(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Carries out the digitwise logical or of `lhs` and `rhs`.
    ///
    /// The operands must be valid for logical operations.
    /// See [`Decimal128::is_logical`].
    pub fn or(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadOr(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }

    /// Carries out the digitwise logical exclusive or of `lhs` and `rhs`.
    ///
    /// The operands must be valid for logical operations.
    /// See [`Decimal128::is_logical`].
    pub fn xor(&mut self, mut lhs: Decimal128, rhs: Decimal128) -> Decimal128 {
        unsafe {
            decnumber_sys::decQuadXor(&mut lhs.inner, &lhs.inner, &rhs.inner, &mut self.inner);
        }
        lhs
    }
}

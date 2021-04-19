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

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::ffi::{CStr, CString};
use std::fmt;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::str::FromStr;

use libc::c_char;

use crate::context::{Class, Context};
use crate::decimal128::Decimal128;
use crate::decimal32::Decimal32;
use crate::decimal64::Decimal64;
use crate::error::{InvalidExponentError, InvalidPrecisionError, ParseDecimalError};

fn validate_n(n: usize) {
    // TODO(benesch): check this at compile time, when that becomes possible.
    if n < 12 || n > 999_999_999 {
        panic!("Decimal<N>:: N is not in the range [12, 999999999]");
    }
}

/// An arbitrary-precision decimal number.
///
/// The maximum number of digits that can be stored in the number is specified
/// by `N * 3`. For example, a value of type `Decimal<3>` has space for nine
/// decimal digits. This somewhat odd design is due to limitations of constant
/// generic parameters in Rust. The intention is to someday make `N` correspond
/// directly to the number of digits of precision.
///
/// `N` must be at least 12 and no greater than 999,999,999, though typically
/// the stack size implies a smaller maximum for `N`. Due to limitations with
/// constant generics it is not yet possible to enforce these restrictions
/// at compile time, so they are checked at runtime.
#[repr(C)]
#[derive(Clone)]
pub struct Decimal<const N: usize> {
    digits: u32,
    exponent: i32,
    bits: u8,
    lsu: [u16; N],
}

impl<const N: usize> Decimal<N> {
    pub(crate) fn as_ptr(&self) -> *const decnumber_sys::decNumber {
        self as *const Decimal<N> as *const decnumber_sys::decNumber
    }

    pub(crate) fn as_mut_ptr(&mut self) -> *mut decnumber_sys::decNumber {
        self as *mut Decimal<N> as *mut decnumber_sys::decNumber
    }

    /// Constructs a decimal number with `N / 3` digits of precision
    /// representing the number 0.
    pub fn zero() -> Decimal<N> {
        Decimal::default()
    }

    /// Constructs a decimal number representing positive infinity.
    pub fn infinity() -> Decimal<N> {
        let mut d = Decimal::default();
        d.bits = decnumber_sys::DECINF;
        d
    }

    /// Constructs a decimal number representing a non-signaling NaN.
    pub fn nan() -> Decimal<N> {
        let mut d = Decimal::default();
        d.bits = decnumber_sys::DECNAN;
        d
    }

    /// Computes the number of significant digits in the number.
    ///
    /// If the number is zero or infinite, returns 1. If the number is a NaN,
    /// returns the number of digits in the payload.
    pub fn digits(&self) -> u32 {
        self.digits
    }

    /// Computes the exponent of the number.
    pub fn exponent(&self) -> i32 {
        self.exponent
    }

    /// Reports whether the number is finite.
    ///
    /// A finite number is one that is neither infinite nor a NaN.
    pub fn is_finite(&self) -> bool {
        (self.bits & decnumber_sys::DECSPECIAL) == 0
    }

    /// Reports whether the number is positive or negative infinity.
    pub fn is_infinite(&self) -> bool {
        (self.bits & decnumber_sys::DECINF) != 0
    }

    /// Reports whether the number is a NaN.
    pub fn is_nan(&self) -> bool {
        (self.bits & (decnumber_sys::DECNAN | decnumber_sys::DECSNAN)) != 0
    }

    /// Reports whether the number is negative.
    ///
    /// A negative number is either negative zero, less than zero, or NaN
    /// with a sign of one. This corresponds to [`Decimal128::is_signed`], not
    /// [`Decimal128::is_negative`].
    pub fn is_negative(&self) -> bool {
        (self.bits & decnumber_sys::DECNEG) != 0
    }

    /// Reports whether the number is a quiet NaN.
    pub fn is_quiet_nan(&self) -> bool {
        (self.bits & decnumber_sys::DECNAN) != 0
    }

    /// Reports whether the number is a signaling NaN.
    pub fn is_signaling_nan(&self) -> bool {
        (self.bits & decnumber_sys::DECSNAN) != 0
    }

    /// Reports whether the number has a special value.
    ///
    /// A special value is either infinity or NaN. This is the inverse of
    /// [`Decimal::is_finite`].
    pub fn is_special(&self) -> bool {
        (self.bits & decnumber_sys::DECSPECIAL) != 0
    }

    /// Reports whether the number is positive or negative zero.
    pub fn is_zero(&self) -> bool {
        self.is_finite() && self.lsu[0] == 0 && self.digits == 1
    }

    /// Reports whether the quantum of the number matches the quantum of
    /// `rhs`.
    ///
    /// Quantums are considered to match if the numbers have the same exponent,
    /// are both NaNs, or both infinite.
    pub fn quantum_matches(&self, rhs: &Decimal<N>) -> bool {
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        let d = unsafe {
            decnumber_sys::decNumberSameQuantum(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                self.as_ptr(),
                rhs.as_ptr(),
            );
            d.assume_init()
        };
        if d.is_zero() {
            false
        } else {
            debug_assert!(!d.is_special());
            true
        }
    }

    /// Converts this decimal to a 32-bit decimal float.
    ///
    /// The result may be inexact. Use [`Context::<Decimal32>::from_decimal`]
    /// to observe exceptional conditions.
    pub fn to_decimal32(&self) -> Decimal32 {
        Context::<Decimal32>::default().from_decimal(self)
    }

    /// Converts this decimal to a 64-bit decimal float.
    ///
    /// The result may be inexact. Use [`Context::<Decimal64>::from_decimal`]
    /// to observe exceptional conditions.
    pub fn to_decimal64(&self) -> Decimal64 {
        Context::<Decimal64>::default().from_decimal(self)
    }

    /// Converts this decimal to a 128-bit decimal float.
    ///
    /// The result may be inexact. Use [`Context::<Decimal128>::from_decimal`]
    /// to observe exceptional conditions.
    pub fn to_decimal128(&self) -> Decimal128 {
        Context::<Decimal128>::default().from_decimal(self)
    }

    /// Returns the raw parts of this decimal.
    ///
    /// The meaning of these parts are unspecified and subject to change.
    pub fn to_raw_parts(&self) -> (u32, i32, u8, [u16; N]) {
        (self.digits, self.exponent, self.bits, self.lsu)
    }
}

impl<const N: usize> Default for Decimal<N> {
    fn default() -> Decimal<N> {
        validate_n(N);
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        unsafe {
            decnumber_sys::decNumberZero(d.as_mut_ptr() as *mut decnumber_sys::decNumber);
            d.assume_init()
        }
    }
}

impl<const N: usize> fmt::Debug for Decimal<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<const N: usize> fmt::Display for Decimal<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // String conversion may need up to `self.digits + 14` characters,
        // per the libdecnumber documentation.
        let mut buf = Vec::with_capacity(self.digits as usize + 14);
        let c_str = unsafe {
            if f.alternate() {
                decnumber_sys::decNumberToEngString(self.as_ptr(), buf.as_mut_ptr() as *mut c_char);
            } else {
                decnumber_sys::decNumberToString(self.as_ptr(), buf.as_mut_ptr() as *mut c_char);
            }
            CStr::from_ptr(buf.as_ptr() as *const c_char)
        };
        f.write_str(
            c_str
                .to_str()
                .expect("decNumberToString yields valid UTF-8"),
        )
    }
}

impl<const N: usize> FromStr for Decimal<N> {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Decimal<N>, ParseDecimalError> {
        Context::<Decimal<N>>::default().parse(s)
    }
}

impl<const N: usize> From<Decimal32> for Decimal<N> {
    fn from(n: Decimal32) -> Decimal<N> {
        validate_n(N);
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        unsafe {
            decnumber_sys::decimal32ToNumber(
                &n.inner,
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
            );
            d.assume_init()
        }
    }
}

impl<const N: usize> From<Decimal64> for Decimal<N> {
    fn from(n: Decimal64) -> Decimal<N> {
        validate_n(N);
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        unsafe {
            decnumber_sys::decimal64ToNumber(
                &n.inner,
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
            );
            d.assume_init()
        }
    }
}

impl<const N: usize> From<Decimal128> for Decimal<N> {
    fn from(n: Decimal128) -> Decimal<N> {
        validate_n(N);
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        unsafe {
            decnumber_sys::decimal128ToNumber(
                &n.inner,
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
            );
            d.assume_init()
        }
    }
}

impl<const N: usize> Default for Context<Decimal<N>> {
    fn default() -> Context<Decimal<N>> {
        let mut ctx = MaybeUninit::<decnumber_sys::decContext>::uninit();
        let mut ctx = unsafe {
            decnumber_sys::decContextDefault(ctx.as_mut_ptr(), decnumber_sys::DEC_INIT_BASE);
            ctx.assume_init()
        };
        ctx.traps = 0;
        // TODO(benesch): this could be a static assertion or a where bound,
        // if either of those were supported.
        ctx.digits = i32::try_from(N * decnumber_sys::DECDPUN)
            .expect("decimal digit count does not fit into i32");
        Context {
            inner: ctx,
            _phantom: PhantomData,
        }
    }
}

impl<const N: usize> Context<Decimal<N>> {
    /// Returns the context's precision.
    ///
    /// Operations that use this context will be rounded to this length if
    /// necessary.
    pub fn precision(&self) -> usize {
        usize::try_from(self.inner.digits).expect("context digit count does not fit into usize")
    }

    /// Sets the context's precision.
    ///
    /// The precision must be greater than one and no greater than `N * 3`.
    pub fn set_precision(&mut self, precision: usize) -> Result<(), InvalidPrecisionError> {
        if precision < 1 || precision > N * decnumber_sys::DECDPUN {
            return Err(InvalidPrecisionError);
        }
        self.inner.digits = i32::try_from(precision).map_err(|_| InvalidPrecisionError)?;
        Ok(())
    }

    /// Reports whether the context has exponent clamping enabled.
    ///
    /// See the `clamp` field in the documentation of libdecnumber's
    /// [decContext module] for details.
    ///
    /// [decContext module]: http://speleotrove.com/decimal/dncont.html
    pub fn clamp(&self) -> bool {
        self.inner.clamp != 0
    }

    /// Sets whether the context has exponent clamping enabled.
    pub fn set_clamp(&mut self, clamp: bool) {
        self.inner.clamp = u8::from(clamp)
    }

    /// Returns the context's maximum exponent.
    ///
    /// See the `emax` field in the documentation of libdecnumber's
    /// [decContext module] for details.
    ///
    /// [decContext module]: http://speleotrove.com/decimal/dncont.html
    pub fn max_exponent(&self) -> isize {
        isize::try_from(self.inner.emax).expect("context max exponent does not fit into isize")
    }

    /// Sets the context's maximum exponent.
    ///
    /// The maximum exponent must not be negative and no greater than
    /// 999,999,999.
    pub fn set_max_exponent(&mut self, e: isize) -> Result<(), InvalidExponentError> {
        if e < 0 || e > 999999999 {
            return Err(InvalidExponentError);
        }
        self.inner.emax = i32::try_from(e).map_err(|_| InvalidExponentError)?;
        Ok(())
    }

    /// Returns the context's minimum exponent.
    ///
    /// See the `emin` field in the documentation of libdecnumber's
    /// [decContext module] for details.
    ///
    /// [decContext module]: http://speleotrove.com/decimal/dncont.html
    pub fn min_exponent(&self) -> isize {
        isize::try_from(self.inner.emin).expect("context min exponent does not fit into isize")
    }

    /// Sets the context's minimum exponent.
    ///
    /// The minimum exponent must not be positive and no smaller than
    /// -999,999,999.
    pub fn set_min_exponent(&mut self, e: isize) -> Result<(), InvalidExponentError> {
        if e > 0 || e < -999999999 {
            return Err(InvalidExponentError);
        }
        self.inner.emin = i32::try_from(e).map_err(|_| InvalidExponentError)?;
        Ok(())
    }

    /// Parses a number from its string representation.
    pub fn parse<S>(&mut self, s: S) -> Result<Decimal<N>, ParseDecimalError>
    where
        S: Into<Vec<u8>>,
    {
        validate_n(N);
        let c_string = CString::new(s).map_err(|_| ParseDecimalError)?;
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        let d = unsafe {
            decnumber_sys::decNumberFromString(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                c_string.as_ptr(),
                &mut self.inner,
            );
            d.assume_init()
        };
        if (self.inner.status & decnumber_sys::DEC_Conversion_syntax) != 0 {
            Err(ParseDecimalError)
        } else {
            Ok(d)
        }
    }

    /// Classifies the number.
    pub fn class(&mut self, n: &Decimal<N>) -> Class {
        Class::from_c(unsafe { decnumber_sys::decNumberClass(n.as_ptr(), &mut self.inner) })
    }

    /// Computes the absolute value of `n`, storing the result in `n`.
    ///
    /// This has the same effect as [`Context::<Decimal<N>>::plus`] unless
    /// `n` is negative, in which case it has the same effect as
    /// [`Context::<Decimal<N>>::minus`].
    pub fn abs(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberAbs(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Adds `lhs` and `rhs`, storing the result in `lhs`.
    pub fn add(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberAdd(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Carries out the digitwise logical and of `lhs` and `rhs`, storing
    /// the result in `lhs`.
    pub fn and(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberAnd(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Divides `lhs` by `rhs`, storing the result in `lhs`.
    pub fn div(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberDivide(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Divides `lhs` by `rhs`, storing the integer part of the result in `lhs`.
    pub fn div_integer(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberDivideInteger(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Raises *e* to the power of `n`, storing the result in `n`.
    pub fn exp(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberExp(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Calculates the fused multiply-add `(x * y) + z` and stores the result
    /// in `x`.
    ///
    /// The multiplication is carried out first and is exact, so this operation
    /// only has the one, final rounding.
    pub fn fma(&mut self, x: &mut Decimal<N>, y: &Decimal<N>, z: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberFMA(
                x.as_mut_ptr(),
                x.as_ptr(),
                y.as_ptr(),
                z.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Computes the digitwise logical inversion of `n`, storing the result in
    /// `n`.
    pub fn invert(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberInvert(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Computes the natural logarithm of `n`, storing the result in `n`.
    pub fn ln(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberLn(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Computes the base-10 logarithm of `n`, storing the result in `n`.
    pub fn log10(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberLog10(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Computes the adjusted exponent of the number, according to IEEE 754
    /// rules.
    pub fn logb(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberLogB(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Places whichever of `lhs` and `rhs` is larger in `lhs`.
    ///
    /// The comparison is performed using the same rules as for
    /// [`total_cmp`](Context::<Decimal128>::total_cmp).
    pub fn max(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberMax(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Places whichever of `lhs` and `rhs` has the larger absolute value in
    /// `lhs`.
    pub fn max_abs(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberMaxMag(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Places whichever of `lhs` and `rhs` is smaller in `lhs`.
    ///
    /// The comparison is performed using the same rules as for
    /// [`total_cmp`](Context::<Decimal128>::total_cmp).
    pub fn min(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberMin(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Places whichever of `lhs` and `rhs` has the smaller absolute value in
    /// `lhs`.
    pub fn min_abs(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberMinMag(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Subtracts `n` from zero, storing the result in `n`.
    pub fn minus(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberMinus(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Multiples `lhs` by `rhs`, storing the result in `lhs`.
    pub fn mul(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberMultiply(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Computes the next number to `n` in the direction of negative infinity,
    /// storing the result in `n`.
    ///
    /// This operation is a generalization of the IEEE 754 *nextDown* operation.
    pub fn next_minus(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberNextMinus(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Computes the next number to `n` in the direction of positive infinity,
    /// storing the result in `n`.
    ///
    /// This operation is a generalization of the IEEE 754 *nextUp* operation.
    pub fn next_plus(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberNextPlus(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Computes the next number to `x` in the direction of `y`, storing the
    /// result in `x`.
    ///
    /// This operation is a generalization of the IEEE 754 *nextAfter*
    /// operation.
    pub fn next_toward(&mut self, x: &mut Decimal<N>, y: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberNextToward(
                x.as_mut_ptr(),
                x.as_ptr(),
                y.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Carries out the digitwise logical or of `lhs` and `rhs`, storing
    /// the result in `lhs`.
    pub fn or(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberOr(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Determines the ordering of `lhs` relative to `rhs`, using a partial
    /// order.
    ///
    /// If either `lhs` or `rhs` is a NaN, returns `None`. To force an ordering
    /// upon NaNs, use [`total_cmp`](Context::<Decimal<N>>::total_cmp).
    pub fn partial_cmp(&mut self, lhs: &Decimal<N>, rhs: &Decimal<N>) -> Option<Ordering> {
        validate_n(N);
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        let d = unsafe {
            decnumber_sys::decNumberCompare(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
            d.assume_init()
        };
        if d.is_nan() {
            None
        } else if d.is_negative() {
            Some(Ordering::Less)
        } else if d.is_zero() {
            Some(Ordering::Equal)
        } else {
            debug_assert!(!d.is_special());
            Some(Ordering::Greater)
        }
    }

    /// Adds `n` to zero, storing the result in `n`.
    pub fn plus(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberPlus(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Raises `x` to the power of `y`, storing the result in `x`.
    pub fn pow(&mut self, x: &mut Decimal<N>, y: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberPower(x.as_mut_ptr(), x.as_ptr(), y.as_ptr(), &mut self.inner);
        }
    }

    /// Rounds or pads `lhs` so that it has the same exponent as `rhs`, storing
    /// the result in `lhs`.
    pub fn quantize(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberQuantize(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Reduces `n`'s coefficient to its shortest possible form without
    /// changing the value of the result, storing the result in `n`.
    pub fn reduce(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberReduce(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Integer-divides `lhs` by `rhs`, storing the remainder in `lhs`.
    pub fn rem(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberRemainder(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Like [`rem`](Context::<Decimal<N>>::rem), but uses the IEEE 754
    /// rules for remainder operations.
    pub fn rem_near(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberRemainderNear(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Rescales `n` to have an exponent of `exp`.
    pub fn rescale(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberRescale(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Shifts the digits of `lhs` by `rhs`, storing the result in `lhs`.
    ///
    /// If `rhs` is positive, shifts to the left. If `rhs` is negative, shifts
    /// to the right. Any digits "shifted in" will be zero.
    ///
    /// `rhs` specifies the number of positions to shift, and must be a finite
    /// integer.
    pub fn shift(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberShift(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Rotates the digits of `lhs` by `rhs`, storing the result in `lhs`.
    ///
    /// If `rhs` is positive, rotates to the left. If `rhs` is negative, rotates
    /// to the right.
    ///
    /// `rhs` specifies the number of positions to rotate, and must be a finite
    /// integer.
    pub fn rotate(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberRotate(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Multiplies `x` by 10<sup>`y`</sup>, storing the result in `x`.
    pub fn scaleb(&mut self, x: &mut Decimal<N>, y: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberScaleB(x.as_mut_ptr(), x.as_ptr(), y.as_ptr(), &mut self.inner);
        }
    }

    /// Computes the square root of `n`, storing the result in `n`.
    pub fn sqrt(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberSquareRoot(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Subtracts `rhs` from `lhs`, storing the result in `lhs`.
    pub fn sub(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberSubtract(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }

    /// Determines the ordering of `lhs` relative to `rhs`, using the
    /// total order predicate defined in IEEE 754-2008.
    ///
    /// For a brief description of the ordering, consult [`f32::total_cmp`].
    pub fn total_cmp(&mut self, lhs: &Decimal<N>, rhs: &Decimal<N>) -> Ordering {
        validate_n(N);
        let mut d = MaybeUninit::<Decimal<N>>::uninit();
        let d = unsafe {
            decnumber_sys::decNumberCompareTotal(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
            d.assume_init()
        };
        debug_assert!(!d.is_special());
        if d.is_negative() {
            Ordering::Less
        } else if d.is_zero() {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }

    /// Carries out the digitwise logical xor of `lhs` and `rhs`, storing
    /// the result in `lhs`.
    pub fn xor(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberXor(
                lhs.as_mut_ptr(),
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            );
        }
    }
}

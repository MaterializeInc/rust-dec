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
use std::convert::{TryFrom, TryInto};
use std::ffi::{CStr, CString};
use std::fmt;
use std::iter::{Product, Sum};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::str::FromStr;

use libc::c_char;
#[cfg(feature = "num-traits")]
use num_traits::{MulAdd, MulAddAssign, Pow, Zero};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::context::{Class, Context};
use crate::decimal128::Decimal128;
use crate::decimal32::Decimal32;
use crate::decimal64::Decimal64;
use crate::error::{
    FromBcdError, InvalidCoefficientError, InvalidExponentError, InvalidPrecisionError,
    ParseDecimalError, TryFromDecimalError, TryIntoDecimalError,
};

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
/// constant generics it is not yet possible to enforce these restrictions at
/// compile time, so they are checked at runtime.
///
/// For more details about e.g. the struct's fields, see the [upstream
/// documentation](http://speleotrove.com/decimal/dnnumb.html).
#[repr(C)]
#[derive(Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Decimal<const N: usize> {
    pub(crate) digits: u32,
    pub(crate) exponent: i32,
    pub(crate) bits: u8,
    /// Must provide custom serde implementation for array defined with const
    /// generic until something happens with
    /// https://github.com/serde-rs/serde/issues/1272
    #[cfg_attr(feature = "serde", serde(with = "lsu_serde"))]
    pub(crate) lsu: [u16; N],
}

#[cfg(feature = "serde")]
/// Provides a target for `serde(with = ...)` that permits deserializing `Decimal` values from
/// primitive integers, `Strings`, or `str`.
///
/// ```rust
/// use std::convert::TryFrom;
/// use serde::{Deserialize, Serialize};
/// const N: usize = 12;
///
/// #[repr(transparent)]
/// #[derive(Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
/// pub struct PrimitiveDeserializableDecimal<const N: usize>(
///     #[serde(with = "dec::serde_decimal_from_non_float_primitives")] pub dec::Decimal<N>,
/// );
///
/// let v: PrimitiveDeserializableDecimal<N> =
///           serde_json::from_str("-1").expect("deserialization works");
///
/// assert_eq!(dec::Decimal::try_from(-1i32).unwrap(), v.0);
/// ```
///
/// Note that the feature provided by this crate is only compatible with self-describing input
/// formats, such as `JSON`, as it relies on [`Deserialize::deserialize_any`](deserialize_any).
///
/// [deserialize_any]:
///     https://docs.rs/serde/latest/serde/trait.Deserializer.html#tymethod.deserialize_any
pub mod serde_decimal_from_non_float_primitives {
    use std::convert::TryFrom;
    use std::fmt;
    use std::str::FromStr;

    use serde::de::{self, MapAccess, SeqAccess, Visitor};
    use serde::{Deserialize, Deserializer, Serialize};

    use crate::Decimal;

    /// Serialize `d` using the default, derivsed `Serialize` implementation.
    pub fn serialize<S, const N: usize>(d: &Decimal<N>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
        Decimal<N>: Serialize,
    {
        Decimal::<N>::serialize(d, serializer)
    }

    /// Deserializes the value permitting a conversion to a `Decimal<N>` from primitive integers
    /// (`i8`, `u8`, `i16`, `u16`, `i32`, `u32`, `i64`, `u64`, `i128`, `u128`), `String`, and `str`.
    pub fn deserialize<'de, D, const N: usize>(deserializer: D) -> Result<Decimal<N>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        enum Field {
            Digits,
            Exponent,
            Bits,
            Lsu,
        }

        impl<'de> Deserialize<'de> for Field {
            fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FieldVisitor;

                impl<'de> Visitor<'de> for FieldVisitor {
                    type Value = Field;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("`digits`, `exponent`, `bits`, or `lsu`")
                    }

                    fn visit_str<E>(self, value: &str) -> Result<Field, E>
                    where
                        E: de::Error,
                    {
                        match value {
                            "digits" => Ok(Field::Digits),
                            "exponent" => Ok(Field::Exponent),
                            "bits" => Ok(Field::Bits),
                            "lsu" => Ok(Field::Lsu),
                            _ => Err(de::Error::unknown_field(value, FIELDS)),
                        }
                    }
                }

                deserializer.deserialize_identifier(FieldVisitor)
            }
        }

        struct DecimalVisitor<const N: usize>;

        macro_rules! deser_try_from {
            ($($t:ty),*) => {
                $(
                    paste::paste! {
                        fn [< visit_ $t >]<E>(self, value: $t) -> Result<Self::Value, E>
                        where
                            E: de::Error,
                        {
                            Decimal::try_from(value).map_err(serde::de::Error::custom)
                        }
                    }
                )*
            };
        }

        impl<'de, const N: usize> Visitor<'de> for DecimalVisitor<N> {
            type Value = Decimal<N>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct Decimal or compatible primitive")
            }

            deser_try_from!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128);

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Decimal::from_str(v).map_err(serde::de::Error::custom)
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Decimal::from_str(&v).map_err(serde::de::Error::custom)
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Decimal<N>, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let digits = seq
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                let exponent = seq
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(1, &self))?;
                let bits = seq
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(2, &self))?;

                let lsu: Vec<u16> = seq
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(3, &self))?;
                let lsu = super::lsu_serde::check_deserialized_vec(lsu)?;

                Ok(Decimal {
                    digits,
                    exponent,
                    bits,
                    lsu,
                })
            }

            fn visit_map<V>(self, mut map: V) -> Result<Decimal<N>, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut digits = None;
                let mut exponent = None;
                let mut bits = None;
                let mut lsu = None;
                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Digits => {
                            if digits.is_some() {
                                return Err(de::Error::duplicate_field("digits"));
                            }
                            digits = Some(map.next_value()?);
                        }
                        Field::Exponent => {
                            if exponent.is_some() {
                                return Err(de::Error::duplicate_field("exponent"));
                            }
                            exponent = Some(map.next_value()?);
                        }
                        Field::Bits => {
                            if bits.is_some() {
                                return Err(de::Error::duplicate_field("bits"));
                            }
                            bits = Some(map.next_value()?);
                        }
                        Field::Lsu => {
                            if lsu.is_some() {
                                return Err(de::Error::duplicate_field("lsu"));
                            }
                            let lsu_deserialized: Vec<u16> = map.next_value()?;
                            let lsu_deserialized =
                                super::lsu_serde::check_deserialized_vec(lsu_deserialized)?;

                            lsu = Some(lsu_deserialized);
                        }
                    }
                }
                let digits = digits.ok_or_else(|| de::Error::missing_field("digits"))?;
                let exponent = exponent.ok_or_else(|| de::Error::missing_field("exponent"))?;
                let bits = bits.ok_or_else(|| de::Error::missing_field("bits"))?;
                let lsu = lsu.ok_or_else(|| de::Error::missing_field("lsu"))?;

                Ok(Decimal {
                    digits,
                    exponent,
                    bits,
                    lsu,
                })
            }
        }

        const FIELDS: &'static [&'static str] = &["digits", "exponent", "bits", "lsu"];
        deserializer.deserialize_any(DecimalVisitor)
    }
}

#[cfg(feature = "serde")]
mod lsu_serde {
    use std::convert::TryInto;

    use serde::de::{Error, Unexpected};
    use serde::ser::SerializeSeq;
    use serde::Deserialize;
    pub fn serialize<S, const N: usize>(v: &[u16; N], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(N))?;
        for e in v.iter() {
            seq.serialize_element(e)?;
        }
        seq.end()
    }

    pub fn deserialize<'de, D, const N: usize>(deserializer: D) -> Result<[u16; N], D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let lsu = Vec::<u16>::deserialize(deserializer)?;
        check_deserialized_vec(lsu)
    }

    // Make this error checking shareable with manual deserialization impls.
    pub fn check_deserialized_vec<const N: usize, E>(lsu: Vec<u16>) -> Result<[u16; N], E>
    where
        E: Error,
    {
        lsu.try_into().map_err(|e: Vec<u16>| {
            Error::invalid_value(
                Unexpected::Other(&format!("&[u16] of length {}", e.len())),
                &format!("&[u16] of length {}", N).as_str(),
            )
        })
    }
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

    // Constructs a decimal number equal to 2^32. We use this value internally
    // to create decimals from primitive integers with more than 32 bits.
    fn two_pow_32() -> Decimal<N> {
        let mut d = Decimal::default();
        d.digits = 10;
        d.lsu[0..4].copy_from_slice(&[296, 967, 294, 4]);
        d
    }

    /// Computes the number of significant digits in the number.
    ///
    /// If the number is zero or infinite, returns 1. If the number is a NaN,
    /// returns the number of digits in the payload.
    pub fn digits(&self) -> u32 {
        self.digits
    }

    /// Returns the individual digits of the coefficient in 8-bit, unpacked
    /// [binary-coded decimal][bcd] format.
    ///
    /// [bcd]: https://en.wikipedia.org/wiki/Binary-coded_decimal
    pub fn coefficient_digits(&self) -> Vec<u8> {
        let mut buf = vec![0; usize::try_from(self.digits()).unwrap()];
        unsafe {
            decnumber_sys::decNumberGetBCD(self.as_ptr(), buf.as_mut_ptr() as *mut u8);
        };
        buf
    }

    /// Returns the digits of the coefficient in [`decNumberUnit`][dnu] format,
    /// which is a vector of `u16`, with element number representing
    /// [`decnumber_sys::DECDPUN`] digits of the coefficient.
    ///
    /// The result is ordered with the least significant digits at index 0.
    ///
    /// [dpd]: http://speleotrove.com/decimal/dnnumb.html
    pub fn coefficient_units(&self) -> &[u16] {
        let units_len = Self::digits_to_lsu_elements_len(self.digits);
        &self.lsu[0..units_len]
    }

    /// Returns the value's coefficient as `T` or errors if not possible.
    ///
    /// All primitive ints are valid for `T`.
    pub fn coefficient<T>(&mut self) -> Result<T, InvalidCoefficientError>
    where
        T: TryFrom<Decimal<N>>,
    {
        // Save current exponent to avoid an allocation.
        let cur_exp = self.exponent();
        // Temporarily set exponent to 0 to make convertible to primitive int
        // `T`.
        self.set_exponent(0);
        let coefficient = <T>::try_from(*self);
        // Revert the exponent to its previous value.
        self.set_exponent(cur_exp);
        match coefficient {
            Ok(d) => Ok(d),
            Err(_) => Err(InvalidCoefficientError),
        }
    }

    /// Returns the number of elements required in the `lsu` to represent some
    /// number of digits.
    ///
    /// This function is public and accepts a `u32` instead of a `Decimal` to
    /// aid in recomposing ([`Self::from_raw_parts`]) values.
    pub fn digits_to_lsu_elements_len(digits: u32) -> usize {
        (usize::try_from(digits).unwrap() + decnumber_sys::DECDPUN - 1) / decnumber_sys::DECDPUN
    }

    /// Computes the exponent of the number.
    pub fn exponent(&self) -> i32 {
        self.exponent
    }

    /// Sets `self`'s exponent to the provided value.
    pub fn set_exponent(&mut self, exponent: i32) {
        self.exponent = exponent;
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
        let mut d = Decimal::<N>::zero();
        unsafe {
            decnumber_sys::decNumberSameQuantum(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                self.as_ptr(),
                rhs.as_ptr(),
            );
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
    /// The meaning of these parts are unspecified and subject to change. The
    /// only guarantee is that these parts can be supplied as arguments to the
    /// [`Decimal::from_raw_parts`] to produce a decimal equivalent to the
    /// original.
    pub fn to_raw_parts(&self) -> (u32, i32, u8, [u16; N]) {
        (self.digits, self.exponent, self.bits, self.lsu)
    }

    /// Returns a `Decimal::<N>` with the supplied raw parts, which should be
    /// generated using [`Decimal::to_raw_parts`].
    pub fn from_raw_parts(digits: u32, exponent: i32, bits: u8, lsu: [u16; N]) -> Self {
        Decimal {
            digits,
            exponent,
            bits,
            lsu,
        }
    }

    /// Returns `self` as a [Packed Decimal][pd] number, including its scale
    /// (i.e. its negated exponent) or `None` for special values.
    ///
    /// [pd]: http://speleotrove.com/decimal/dnpack.html
    pub fn to_packed_bcd(&mut self) -> Option<(Vec<u8>, i32)> {
        if self.is_special() {
            return None;
        }
        let mut len = (usize::try_from(self.digits).unwrap() + 1) / 2;
        if self.digits % 2 == 0 {
            // Ensure space for sign nibble
            len += 1;
        }

        let mut bcd = vec![0; len];
        let mut scale: i32 = 0;
        let ret = unsafe {
            decnumber_sys::decPackedFromNumber(
                bcd.as_mut_ptr() as *mut u8,
                len.try_into().unwrap(),
                &mut scale as *mut i32,
                self.as_mut_ptr() as *mut decnumber_sys::decNumber,
            )
        };
        // Null returned only for special values (already handled) or if `self`
        // didn't fit within `bcd` (shouldn't happen).
        assert!(!ret.is_null());
        Some((bcd, scale))
    }

    /// Takes [Packed Decimal][pd] values and their scales (generated by
    /// [`Self::to_packed_bcd`]) and returns a `Decimal`.
    ///
    /// # Errors
    ///
    /// - `bcd` contains more digits than the coefficient permits
    /// - The adjusted exponent is out of range
    /// - No sign nibble was found
    /// - A sign nibble was found before the final nibble
    ///
    /// [pd]: http://speleotrove.com/decimal/dnpack.html
    pub fn from_packed_bcd(bcd: &[u8], scale: i32) -> Result<Decimal<N>, FromBcdError> {
        let mut d = Decimal::default();
        let ret = unsafe {
            decnumber_sys::decPackedToNumber(
                bcd.as_ptr() as *const u8,
                bcd.len().try_into().unwrap(),
                &scale as *const i32,
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
            )
        };

        if ret.is_null() {
            Err(FromBcdError)
        } else {
            Ok(d)
        }
    }

    /// Returns a string of the number in standard notation, i.e. guaranteed to
    /// not be scientific notation.
    pub fn to_standard_notation_string(&self) -> String {
        if !self.is_finite() {
            return self.to_string();
        }
        let digits = self.coefficient_digits();
        let digits = {
            let i = digits
                .iter()
                .position(|d| *d != 0)
                .unwrap_or(digits.len() - 1);
            &digits[i..]
        };
        let ndigits = digits.len() as i32;
        let e = self.exponent();
        // We allocate space for all the digits plus a possible "-0." prefix.
        // This is usually an overestimate but is an underestimate for very
        // large or very small scales.
        let mut out = String::with_capacity(digits.len() + 3);
        if self.is_negative() {
            out.push('-');
        }

        if e >= 0 {
            // All digits before the decimal point.
            for d in digits {
                out.push(char::from(b'0' + *d));
            }
            if !self.is_zero() {
                for _ in 0..e {
                    out.push('0');
                }
            }
        } else if ndigits > -e {
            // Digits span the decimal point.
            let e = (ndigits + e) as usize;
            for d in &digits[..e] {
                out.push(char::from(b'0' + *d));
            }
            out.push('.');
            for d in &digits[e..] {
                out.push(char::from(b'0' + *d));
            }
        } else {
            // All digits after the decimal point.
            out.push_str("0.");
            for _ in 0..(-e - ndigits) {
                out.push('0');
            }
            for d in digits {
                out.push(char::from(b'0' + *d));
            }
        }
        out
    }

    /// Removes insignificant trailing zeros from a number, unconditionally, and
    /// stores the modified value in `self`.
    pub fn trim(&mut self) {
        unsafe {
            decnumber_sys::decNumberTrim(self.as_mut_ptr());
        }
    }
}

impl<const N: usize> Default for Decimal<N> {
    fn default() -> Decimal<N> {
        validate_n(N);
        Decimal::<N> {
            digits: 1,
            bits: 0,
            exponent: 0,
            lsu: [0; N],
        }
    }
}

impl<const N: usize> PartialOrd for Decimal<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Context::<Decimal<N>>::default().partial_cmp(self, other)
    }
}

impl<const N: usize> PartialEq for Decimal<N> {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl<const N: usize> Neg for Decimal<N> {
    type Output = Decimal<N>;

    /// Note that this clones `self` to generate the negative value. For a
    /// non-cloning method, use `Context::<N>::neg`.
    fn neg(self) -> Decimal<N> {
        let mut n = self.clone();
        let n_ptr = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberCopyNegate(n_ptr, n_ptr);
        }
        n
    }
}

impl<const M: usize, const N: usize> Add<Decimal<M>> for Decimal<N> {
    type Output = Self;

    /// Note that this clones `self` to generate the output. For a
    /// non-cloning method, use `Context::<N>::add`.
    fn add(self, rhs: Decimal<M>) -> Self {
        let mut lhs = self.clone();
        Context::<Self>::default().add(&mut lhs, &rhs);
        lhs
    }
}

impl<const M: usize, const N: usize> AddAssign<Decimal<M>> for Decimal<N> {
    fn add_assign(&mut self, rhs: Decimal<M>) {
        Context::<Self>::default().add(self, &rhs);
    }
}

impl<const M: usize, const N: usize> Div<Decimal<M>> for Decimal<N> {
    type Output = Self;

    /// Note that this clones `self` to generate the output. For a
    /// non-cloning method, use `Context::<N>::div`.
    fn div(self, rhs: Decimal<M>) -> Self {
        let mut lhs = self.clone();
        Context::<Self>::default().div(&mut lhs, &rhs);
        lhs
    }
}

impl<const M: usize, const N: usize> DivAssign<Decimal<M>> for Decimal<N> {
    fn div_assign(&mut self, rhs: Decimal<M>) {
        Context::<Self>::default().div(self, &rhs);
    }
}

impl<const M: usize, const N: usize> Mul<Decimal<M>> for Decimal<N> {
    type Output = Self;

    /// Note that this clones `self` to generate the output. For a
    /// non-cloning method, use `Context::<N>::mul`.
    fn mul(self, rhs: Decimal<M>) -> Self {
        let mut lhs = self.clone();
        Context::<Self>::default().mul(&mut lhs, &rhs);
        lhs
    }
}

impl<const M: usize, const N: usize> MulAssign<Decimal<M>> for Decimal<N> {
    fn mul_assign(&mut self, rhs: Decimal<M>) {
        Context::<Self>::default().mul(self, &rhs);
    }
}

impl<const M: usize, const N: usize> Rem<Decimal<M>> for Decimal<N> {
    type Output = Self;

    /// Note that this clones `self` to generate the output. For a
    /// non-cloning method, use `Context::<N>::rem`.
    fn rem(self, rhs: Decimal<M>) -> Self {
        let mut lhs = self.clone();
        Context::<Self>::default().rem(&mut lhs, &rhs);
        lhs
    }
}

impl<const M: usize, const N: usize> RemAssign<Decimal<M>> for Decimal<N> {
    fn rem_assign(&mut self, rhs: Decimal<M>) {
        Context::<Self>::default().rem(self, &rhs);
    }
}

impl<const M: usize, const N: usize> Sub<Decimal<M>> for Decimal<N> {
    type Output = Self;

    /// Note that this clones `self` to generate the output. For a
    /// non-cloning method, use `Context::<N>::sub`.
    fn sub(self, rhs: Decimal<M>) -> Self {
        let mut lhs = self.clone();
        Context::<Self>::default().sub(&mut lhs, &rhs);
        lhs
    }
}

impl<const M: usize, const N: usize> SubAssign<Decimal<M>> for Decimal<N> {
    fn sub_assign(&mut self, rhs: Decimal<M>) {
        Context::<Self>::default().sub(self, &rhs);
    }
}

impl<const M: usize, const N: usize> Sum<Decimal<M>> for Decimal<N> {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Decimal<M>>,
    {
        iter.map(|v| v).collect::<Vec<_>>().iter().sum()
    }
}

impl<'a, const M: usize, const N: usize> Sum<&'a Decimal<M>> for Decimal<N> {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Decimal<M>>,
    {
        let mut cx = Context::<Self>::default();
        cx.sum(iter)
    }
}

impl<const M: usize, const N: usize> Product<Decimal<M>> for Decimal<N> {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Decimal<M>>,
    {
        iter.map(|v| v).collect::<Vec<_>>().iter().product()
    }
}

impl<'a, const M: usize, const N: usize> Product<&'a Decimal<M>> for Decimal<N> {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Decimal<M>>,
    {
        let mut cx = Context::<Self>::default();
        cx.product(iter)
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

/// Implements `std::convert::TryInto` semantics for `Decimal<N>` (represented
/// by `$d`) into primitive integers (`$p`).
macro_rules! __decnum_tryinto_primitive {
    ($p:ty, $cx:expr, $max_digits:literal, $d:expr, $allow_neg:expr) => {{
        $cx.rescale(&mut $d, &Decimal::<N>::zero());

        // inexact indicates you rounded away non-zero digits during rescale.
        let inexact = $cx.status().inexact();

        let mut fail = || -> TryFromDecimalError {
            let mut s = $cx.status();
            s.set_invalid_operation();
            $cx.set_status(s);
            TryFromDecimalError
        };

        if $d.is_special()
            || $d.digits() > $max_digits
            || (!$allow_neg && $d.is_negative())
            || inexact
        {
            return Err(fail());
        }

        let accum_op = if $d.is_negative() {
            <$p>::checked_sub
        } else {
            <$p>::checked_add
        };
        let ten: $p = 10;
        let mut ten_pow = 0;

        let mut accum = 0;
        // try-catch
        || -> Option<$p> {
            for v in $d.coefficient_units() {
                let d = <$p>::from(*v).checked_mul(ten.pow(ten_pow))?;
                accum = accum_op(accum, d)?;
                ten_pow += decnumber_sys::DECDPUN as u32;
            }
            Some(accum)
        }()
        .ok_or_else(|| fail())
    }};
}

macro_rules! decnum_tryinto_primitive_int {
    ($p:ty, $cx:expr, $max_digits:literal, $d:expr) => {{
        __decnum_tryinto_primitive!($p, $cx, $max_digits, $d, true)
    }};
}

macro_rules! decnum_tryinto_primitive_uint {
    ($p:ty, $cx:expr, $max_digits:literal, $d:expr) => {{
        __decnum_tryinto_primitive!($p, $cx, $max_digits, $d, false)
    }};
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for i8 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<i8, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_i8(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for u8 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<u8, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_u8(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for i16 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<i16, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_i16(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for u16 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<u16, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_u16(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for i32 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<i32, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_i32(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for u32 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<u32, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_u32(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for i64 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<i64, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_i64(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for u64 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<u64, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_u64(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for i128 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<i128, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_i128(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for u128 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<u128, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_u128(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for usize {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<usize, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_usize(n)
    }
}

/// Refer to the comments on [`Context<Decimal<N>>::try_into_i32()`], which also apply to
/// this trait.
impl<const N: usize> TryFrom<Decimal<N>> for isize {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<isize, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_isize(n)
    }
}

macro_rules! decnum_tryinto_primitive_float {
    ($p:ty, $cx:expr, $d:expr) => {{
        if $d.is_infinite() {
            return Ok(if $d.is_negative() {
                <$p>::NEG_INFINITY
            } else {
                <$p>::INFINITY
            });
        }
        if $d.is_nan() {
            return Ok(<$p>::NAN);
        }

        const TEN: $p = 10.0;
        const DECDPUN_F: $p = decnumber_sys::DECDPUN as $p;

        let mut e = $d.exponent() as $p;
        let mut f: $p = 0.0;
        for u in $d.coefficient_units() {
            // `powi` gives wrong results on some input, whereas `powf` does not
            f += <$p>::from(*u) * TEN.powf(e);
            e += DECDPUN_F;
        }
        if $d.is_negative() {
            f = -f;
        }

        // Value over- or underflows $p:
        // - f.is_infinite() represents generic overflow
        // - f.is_nan() can occur when multiplying a coefficient unit by a power
        //   of 10 that exceeds the primitive type's maximum exponent
        // - (!$d.is_zero() && f == 0.0) represents underflow
        if f.is_infinite() || f.is_nan() || (!$d.is_zero() && f == 0.0) {
            let mut s = $cx.status();
            s.set_invalid_operation();
            $cx.set_status(s);
            Err(TryFromDecimalError)
        } else {
            Ok(f)
        }
    }};
}

impl<const N: usize> TryFrom<Decimal<N>> for f32 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<f32, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_f32(n)
    }
}

impl<const N: usize> TryFrom<Decimal<N>> for f64 {
    type Error = TryFromDecimalError;
    fn try_from(n: Decimal<N>) -> Result<f64, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.try_into_f64(n)
    }
}

impl<const N: usize> From<f32> for Decimal<N> {
    fn from(n: f32) -> Decimal<N> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.from_f32(n)
    }
}

impl<const N: usize> From<f64> for Decimal<N> {
    fn from(n: f64) -> Decimal<N> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.from_f64(n)
    }
}

impl<const N: usize> From<i8> for Decimal<N> {
    fn from(n: i8) -> Decimal<N> {
        Decimal::<N>::from(i32::from(n))
    }
}

impl<const N: usize> From<u8> for Decimal<N> {
    fn from(n: u8) -> Decimal<N> {
        Decimal::<N>::from(u32::from(n))
    }
}

impl<const N: usize> From<i16> for Decimal<N> {
    fn from(n: i16) -> Decimal<N> {
        Decimal::<N>::from(i32::from(n))
    }
}

impl<const N: usize> From<u16> for Decimal<N> {
    fn from(n: u16) -> Decimal<N> {
        Decimal::<N>::from(u32::from(n))
    }
}

impl<const N: usize> From<i32> for Decimal<N> {
    fn from(n: i32) -> Decimal<N> {
        let mut d = Decimal::default();
        unsafe {
            decnumber_sys::decNumberFromInt32(d.as_mut_ptr() as *mut decnumber_sys::decNumber, n);
        }
        d
    }
}

impl<const N: usize> From<u32> for Decimal<N> {
    fn from(n: u32) -> Decimal<N> {
        let mut d = Decimal::default();
        unsafe {
            decnumber_sys::decNumberFromUInt32(d.as_mut_ptr() as *mut decnumber_sys::decNumber, n);
        }
        d
    }
}

impl<const N: usize> From<i64> for Decimal<N> {
    fn from(n: i64) -> Decimal<N> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.from_i64(n)
    }
}

impl<const N: usize> From<u64> for Decimal<N> {
    fn from(n: u64) -> Decimal<N> {
        let mut cx = Context::<Decimal<N>>::default();
        cx.from_u64(n)
    }
}

/// Generates a [`Decimal`] from an `i128` or fails if the result would be
/// imprecise, e.g. has more than `N*3` digits of precision.
///
/// For an infallible version of this function, see
/// [`Context<Decimal<N>>::from_i128`].
impl<const N: usize> TryFrom<i128> for Decimal<N> {
    type Error = TryIntoDecimalError;
    fn try_from(n: i128) -> Result<Decimal<N>, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.from_i128(n);
        return if cx.status().any() {
            Err(TryIntoDecimalError)
        } else {
            Ok(d)
        };
    }
}

/// Generates a [`Decimal`] from a `u128` or fails if the result would be
/// imprecise, e.g. has more than `N*3` digits of precision.
///
/// For an infallible version of this function, see
/// [`Context<Decimal<N>>::from_u128`].
impl<const N: usize> TryFrom<u128> for Decimal<N> {
    type Error = TryIntoDecimalError;
    fn try_from(n: u128) -> Result<Decimal<N>, Self::Error> {
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.from_u128(n);
        return if cx.status().any() {
            Err(TryIntoDecimalError)
        } else {
            Ok(d)
        };
    }
}

#[cfg(target_pointer_width = "32")]
impl<const N: usize> From<usize> for Decimal<N> {
    fn from(n: usize) -> Decimal<N> {
        Decimal::<N>::from(n as u32)
    }
}

#[cfg(target_pointer_width = "32")]
impl<const N: usize> From<isize> for Decimal<N> {
    fn from(n: isize) -> Decimal<N> {
        Decimal::<N>::from(n as i32)
    }
}

#[cfg(target_pointer_width = "64")]
impl<const N: usize> From<usize> for Decimal<N> {
    fn from(n: usize) -> Decimal<N> {
        Decimal::<N>::from(n as u64)
    }
}

#[cfg(target_pointer_width = "64")]
impl<const N: usize> From<isize> for Decimal<N> {
    fn from(n: isize) -> Decimal<N> {
        Decimal::<N>::from(n as i64)
    }
}

impl<const N: usize> From<Decimal32> for Decimal<N> {
    fn from(n: Decimal32) -> Decimal<N> {
        let mut d = Decimal::default();
        unsafe {
            decnumber_sys::decimal32ToNumber(
                &n.inner,
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
            );
        }
        d
    }
}

impl<const N: usize> From<Decimal64> for Decimal<N> {
    fn from(n: Decimal64) -> Decimal<N> {
        let mut d = Decimal::default();
        unsafe {
            decnumber_sys::decimal64ToNumber(
                &n.inner,
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
            );
        }
        d
    }
}

impl<const N: usize> From<Decimal128> for Decimal<N> {
    fn from(n: Decimal128) -> Decimal<N> {
        let mut d = Decimal::default();
        unsafe {
            decnumber_sys::decimal128ToNumber(
                &n.inner,
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
            );
        }
        d
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
    /// The precision must be at least one and no greater than `N * 3`.
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
        let c_string = CString::new(s).map_err(|_| ParseDecimalError)?;
        self.parse_c_str(c_string.as_c_str())
    }

    /// Parses a number from its string representation.
    pub fn parse_c_str(&mut self, s: &CStr) -> Result<Decimal<N>, ParseDecimalError> {
        validate_n(N);
        let mut d = Decimal::zero();
        unsafe {
            decnumber_sys::decNumberFromString(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                s.as_ptr(),
                &mut self.inner,
            );
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
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberAbs(n, n, &mut self.inner);
        }
    }

    /// Adds `lhs` and `rhs`, storing the result in `lhs`.
    pub fn add<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberAdd(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Carries out the digitwise logical and of `lhs` and `rhs`, storing
    /// the result in `lhs`.
    pub fn and<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberAnd(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Divides `lhs` by `rhs`, storing the result in `lhs`.
    pub fn div<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberDivide(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Divides `lhs` by `rhs`, storing the integer part of the result in `lhs`.
    pub fn div_integer<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberDivideInteger(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Raises *e* to the power of `n`, storing the result in `n`.
    pub fn exp(&mut self, n: &mut Decimal<N>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberExp(n, n, &mut self.inner);
        }
    }

    /// Calculates the fused multiply-add `(x * y) + z` and stores the result
    /// in `x`.
    ///
    /// The multiplication is carried out first and is exact, so this operation
    /// only has the one, final rounding.
    pub fn fma<const L: usize, const M: usize>(
        &mut self,
        x: &mut Decimal<N>,
        y: &Decimal<L>,
        z: &Decimal<M>,
    ) {
        let x = x.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberFMA(x, x, y.as_ptr(), z.as_ptr(), &mut self.inner);
        }
    }

    /// Constructs a number from an `i32`.
    pub fn from_i32(&mut self, n: i32) -> Decimal<N> {
        Decimal::<N>::from(n)
    }

    /// Constructs a number from an `i32`.
    pub fn from_u32(&mut self, n: u32) -> Decimal<N> {
        Decimal::<N>::from(n)
    }

    /// Constructs a number from an `i64`.
    pub fn from_i64(&mut self, n: i64) -> Decimal<N> {
        decimal_from_signed_int!(self, n)
    }

    /// Constructs a number from a `u64`.
    pub fn from_u64(&mut self, n: u64) -> Decimal<N> {
        decimal_from_unsigned_int!(self, n)
    }

    /// Constructs a number from an `i128`.
    ///
    /// Note that this function can return inexact results for numbers with more
    /// than `N` * 3 places of precision, e.g. where `N` is 12,
    /// `9_999_999_999_999_999_999_999_999_999_999_999_999i128`,
    /// `-9_999_999_999_999_999_999_999_999_999_999_999_999i128`, `i128::MAX`,
    /// `i128::MIN`, etc.
    ///
    /// However, some numbers more than `N` * 3 places of precision retain their
    /// exactness, e.g. `1_000_000_000_000_000_000_000_000_000_000_000_000i128`.
    ///
    /// ```
    /// const N: usize = 12;
    /// use dec::Decimal;
    /// let mut ctx = dec::Context::<Decimal::<N>>::default();
    /// let d = ctx.from_i128(i128::MAX);
    /// // Inexact result
    /// assert!(ctx.status().inexact());
    ///
    /// let mut ctx = dec::Context::<Decimal::<N>>::default();
    /// let d = ctx.from_i128(1_000_000_000_000_000_000_000_000_000_000_000_000i128);
    /// // Exact result
    /// assert!(!ctx.status().inexact());
    /// ```
    ///
    /// To avoid inexact results when converting from large `i64`, use
    /// [`crate::Decimal128`] instead.
    pub fn from_i128(&mut self, n: i128) -> Decimal<N> {
        decimal_from_signed_int!(self, n)
    }

    /// Constructs a number from an `u128`.
    ///
    /// Note that this function can return inexact results for numbers with more
    /// than `N` * 3 places of precision, e.g. where `N` is 12,
    /// `10_000_000_000_000_000_000_000_000_000_000_001u128` and `u128::MAX`.
    ///
    /// However, some numbers more than `N` * 3 places of precision retain their
    /// exactness,  e.g. `10_000_000_000_000_000_000_000_000_000_000_000u128`.
    ///
    /// ```
    /// const N: usize = 12;
    /// use dec::Decimal;
    /// let mut ctx = dec::Context::<Decimal::<N>>::default();
    /// let d = ctx.from_u128(u128::MAX);
    /// // Inexact result
    /// assert!(ctx.status().inexact());
    ///
    /// let mut ctx = dec::Context::<Decimal::<N>>::default();
    /// let d = ctx.from_u128(1_000_000_000_000_000_000_000_000_000_000_000_000u128);
    /// // Exact result
    /// assert!(!ctx.status().inexact());
    /// ```
    pub fn from_u128(&mut self, n: u128) -> Decimal<N> {
        decimal_from_unsigned_int!(self, n)
    }

    /// Attempts to convert `d` to `u8` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_u8(&mut self, d: Decimal<N>) -> Result<u8, TryFromDecimalError> {
        let i = self.try_into_u32(d)?;
        u8::try_from(i).map_err(|_| TryFromDecimalError)
    }

    /// Attempts to convert `d` to `i8` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_i8(&mut self, d: Decimal<N>) -> Result<i8, TryFromDecimalError> {
        let i = self.try_into_i32(d)?;
        i8::try_from(i).map_err(|_| TryFromDecimalError)
    }

    /// Attempts to convert `d` to `u16` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_u16(&mut self, d: Decimal<N>) -> Result<u16, TryFromDecimalError> {
        let i = self.try_into_u32(d)?;
        u16::try_from(i).map_err(|_| TryFromDecimalError)
    }

    /// Attempts to convert `d` to `i16` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_i16(&mut self, d: Decimal<N>) -> Result<i16, TryFromDecimalError> {
        let i = self.try_into_i32(d)?;
        i16::try_from(i).map_err(|_| TryFromDecimalError)
    }

    /// Attempts to convert `d` to `i32` or fails if not possible. Note that
    /// when returning an error, `self`'s [`context::Status`] is set to
    /// `invalid_operation` in addition to using Rust's `Err` return value.
    ///
    /// Note that this function:
    /// - Accepts any value that can be rescaled to an exponent of 0 without
    ///   becoming inexact. For example, `123.000` and `123E2` are valid
    ///   `Decimal` values.
    ///
    ///   The corollary is that values that cannot be rescaled to an exponent of
    ///   0 error.
    /// - Errors if `self.status()` is set to `invalid_operation` irrespective
    ///   of whether or not this specific invocation of the function set that
    ///   status.
    pub fn try_into_i32(&mut self, mut d: Decimal<N>) -> Result<i32, TryFromDecimalError> {
        self.rescale(&mut d, &Decimal::<N>::zero());
        let i = unsafe { decnumber_sys::decNumberToInt32(d.as_ptr(), &mut self.inner) };
        // inexact indicates you rounded away non-zero digits during rescale.
        if self.status().invalid_operation() || self.status().inexact() {
            Err(TryFromDecimalError)
        } else {
            Ok(i)
        }
    }

    /// Attempts to convert `d` to `u32` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_u32(&mut self, mut d: Decimal<N>) -> Result<u32, TryFromDecimalError> {
        self.rescale(&mut d, &Decimal::<N>::zero());
        let i = unsafe { decnumber_sys::decNumberToUInt32(d.as_ptr(), &mut self.inner) };
        // inexact indicates you rounded away non-zero digits during rescale.
        if self.status().invalid_operation() || self.status().inexact() {
            Err(TryFromDecimalError)
        } else {
            Ok(i)
        }
    }

    /// Attempts to convert `d` to `isize` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    #[cfg(target_pointer_width = "32")]
    pub fn try_into_isize(&mut self, d: Decimal<N>) -> Result<isize, TryFromDecimalError> {
        let d = self.try_into_i32(d)?;
        Ok(d as isize)
    }

    /// Attempts to convert `d` to `isize` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    #[cfg(target_pointer_width = "64")]
    pub fn try_into_isize(&mut self, d: Decimal<N>) -> Result<isize, TryFromDecimalError> {
        let d = self.try_into_i64(d)?;
        Ok(d as isize)
    }

    /// Attempts to convert `d` to `i64` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_i64(&mut self, mut d: Decimal<N>) -> Result<i64, TryFromDecimalError> {
        decnum_tryinto_primitive_int!(i64, self, 19, d)
    }

    /// Attempts to convert `d` to `i128` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_i128(&mut self, mut d: Decimal<N>) -> Result<i128, TryFromDecimalError> {
        decnum_tryinto_primitive_int!(i128, self, 39, d)
    }

    /// Attempts to convert `d` to `usize` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    #[cfg(target_pointer_width = "32")]
    pub fn try_into_usize(&mut self, d: Decimal<N>) -> Result<usize, TryFromDecimalError> {
        let d = self.try_into_u32(d)?;
        Ok(d as usize)
    }

    /// Attempts to convert `d` to `usize` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    #[cfg(target_pointer_width = "64")]
    pub fn try_into_usize(&mut self, d: Decimal<N>) -> Result<usize, TryFromDecimalError> {
        let d = self.try_into_u64(d)?;
        Ok(d as usize)
    }

    /// Attempts to convert `d` to `u64` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_u64(&mut self, mut d: Decimal<N>) -> Result<u64, TryFromDecimalError> {
        decnum_tryinto_primitive_uint!(u64, self, 20, d)
    }

    /// Attempts to convert `d` to `u128` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_i32()`], which also apply to this
    /// function.
    pub fn try_into_u128(&mut self, mut d: Decimal<N>) -> Result<u128, TryFromDecimalError> {
        decnum_tryinto_primitive_uint!(u128, self, 39, d)
    }

    /// Attempts to convert `d` to `f32` or fails if not possible.
    ///
    /// Note that this function:
    /// - Errors for values that over- or underflow `f32`, rather than returning
    ///   infinity or `0.0`, respectively.
    /// - Returns a primitive infinity or NaN if `d` is an equivalent value.
    pub fn try_into_f32(&mut self, d: Decimal<N>) -> Result<f32, TryFromDecimalError> {
        decnum_tryinto_primitive_float!(f32, self, d)
    }

    /// Attempts to convert `d` to `f32` or fails if not possible.
    ///
    /// Refer to the comments on [`Self::try_into_f32()`], which also apply to this
    /// function.
    pub fn try_into_f64(&mut self, d: Decimal<N>) -> Result<f64, TryFromDecimalError> {
        decnum_tryinto_primitive_float!(f64, self, d)
    }

    /// Converts an `f32` to a `Decimal<N>`.
    ///
    /// Note that this conversion is infallible because `f32`'s:
    /// - Maximum precision is ~8
    /// - Min/max exponent is ~ -37, 37
    ///
    /// Both of these are guaranteed to fit comfortably within `Decimal`'s
    /// constraints.
    pub fn from_f32(&mut self, n: f32) -> Decimal<N> {
        self.parse(n.to_string().as_str()).unwrap()
    }

    /// Converts an `f64` to a `Decimal<N>`.
    ///
    /// Note that this conversion is infallible because `f64`'s:
    /// - Maximum precision is ~18
    /// - Min/max exponent is ~ -305, 305
    ///
    /// Both of these are guaranteed to fit comfortably within `Decimal`'s
    /// constraints.
    pub fn from_f64(&mut self, n: f64) -> Decimal<N> {
        self.parse(n.to_string().as_str()).unwrap()
    }

    /// Computes the digitwise logical inversion of `n`, storing the result in
    /// `n`.
    pub fn invert(&mut self, n: &mut Decimal<N>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberInvert(n, n, &mut self.inner);
        }
    }

    /// Computes the natural logarithm of `n`, storing the result in `n`.
    pub fn ln(&mut self, n: &mut Decimal<N>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberLn(n, n, &mut self.inner);
        }
    }

    /// Computes the base-10 logarithm of `n`, storing the result in `n`.
    pub fn log10(&mut self, n: &mut Decimal<N>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberLog10(n, n, &mut self.inner);
        }
    }

    /// Computes the adjusted exponent of the number, according to IEEE 754
    /// rules.
    pub fn logb(&mut self, n: &mut Decimal<N>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberLogB(n, n, &mut self.inner);
        }
    }

    /// Places whichever of `lhs` and `rhs` is larger in `lhs`.
    ///
    /// The comparison is performed using the same rules as for
    /// [`total_cmp`](Context::<Decimal128>::total_cmp).
    pub fn max<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberMax(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Places whichever of `lhs` and `rhs` has the larger absolute value in
    /// `lhs`.
    pub fn max_abs<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberMaxMag(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Places whichever of `lhs` and `rhs` is smaller in `lhs`.
    ///
    /// The comparison is performed using the same rules as for
    /// [`total_cmp`](Context::<Decimal128>::total_cmp).
    pub fn min<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberMin(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Places whichever of `lhs` and `rhs` has the smaller absolute value in
    /// `lhs`.
    pub fn min_abs<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberMinMag(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Subtracts `n` from zero, storing the result in `n`.
    pub fn minus(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberMinus(n.as_mut_ptr(), n.as_ptr(), &mut self.inner);
        }
    }

    /// Multiples `lhs` by `rhs`, storing the result in `lhs`.
    pub fn mul<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberMultiply(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Negates the sign of `n`, storing the result in `n`. Note that unlike
    /// `minus`, no exception or error can occur.
    pub fn neg(&mut self, n: &mut Decimal<N>) {
        unsafe {
            decnumber_sys::decNumberCopyNegate(n.as_mut_ptr(), n.as_ptr());
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
    pub fn next_toward<const M: usize>(&mut self, x: &mut Decimal<N>, y: &Decimal<M>) {
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
    pub fn or<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberOr(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Determines the ordering of `lhs` relative to `rhs`, using a partial
    /// order.
    ///
    /// If either `lhs` or `rhs` is a NaN, returns `None`. To force an ordering
    /// upon NaNs, use [`total_cmp`](Context::<Decimal<N>>::total_cmp).
    pub fn partial_cmp<const L: usize, const M: usize>(
        &mut self,
        lhs: &Decimal<L>,
        rhs: &Decimal<M>,
    ) -> Option<Ordering> {
        validate_n(N);
        let mut d = Decimal::<N>::zero();
        unsafe {
            decnumber_sys::decNumberCompare(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            )
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
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberPlus(n, n, &mut self.inner);
        }
    }

    /// Raises `x` to the power of `y`, storing the result in `x`.
    pub fn pow<const M: usize>(&mut self, x: &mut Decimal<N>, y: &Decimal<M>) {
        let x = x.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberPower(x, x, y.as_ptr(), &mut self.inner);
        }
    }

    /// Takes product of elements in `iter`.
    pub fn product<'a, I, const M: usize>(&mut self, iter: I) -> Decimal<N>
    where
        I: Iterator<Item = &'a Decimal<M>>,
    {
        iter.fold(Decimal::<N>::from(1), |mut product, d| {
            self.mul(&mut product, &d);
            product
        })
    }

    /// Rounds or pads `lhs` so that it has the same exponent as `rhs`, storing
    /// the result in `lhs`.
    pub fn quantize<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberQuantize(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Reduces `n`'s coefficient to its shortest possible form without
    /// changing the value of the result, storing the result in `n`.
    pub fn reduce(&mut self, n: &mut Decimal<N>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberReduce(n, n, &mut self.inner);
        }
    }

    /// Integer-divides `lhs` by `rhs`, storing the remainder in `lhs`.
    pub fn rem<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberRemainder(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Like [`rem`](Context::<Decimal<N>>::rem), but uses the IEEE 754
    /// rules for remainder operations.
    pub fn rem_near<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberRemainderNear(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Rescales `lhs` to have an exponent of `rhs`.
    pub fn rescale<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberRescale(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Rounds the number to an integral value using the rounding mode in the
    /// context.
    pub fn round(&mut self, n: &mut Decimal<N>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberToIntegralExact(n, n, &mut self.inner);
        }
    }

    /// Rounds `n` at a given "place from the left" in the number, akin to a
    /// shift right, round, and shift left.
    ///
    /// Note that this rounding will not drop integral digits (i.e those
    /// representing values at least 1), but can round off fractional values.
    ///
    /// `place` must be at least one and no greater than `N * 3`, i.e. a valid
    /// precision.
    pub fn round_to_place(
        &mut self,
        n: &mut Decimal<N>,
        place: usize,
    ) -> Result<(), InvalidPrecisionError> {
        let precision = self.precision();
        self.set_precision(place)?;
        self.plus(n);
        self.set_precision(precision)
    }

    /// Identical to [`round_to_place`] but simultaneously performs a [`reduce`]
    /// operation, as well.
    pub fn round_reduce_to_place(
        &mut self,
        n: &mut Decimal<N>,
        place: usize,
    ) -> Result<(), InvalidPrecisionError> {
        let precision = self.precision();
        self.set_precision(place)?;
        self.reduce(n);
        self.set_precision(precision)
    }

    /// Shifts the digits of `lhs` by `rhs`, storing the result in `lhs`.
    ///
    /// If `rhs` is positive, shifts to the left. If `rhs` is negative, shifts
    /// to the right. Any digits "shifted in" will be zero.
    ///
    /// `rhs` specifies the number of positions to shift, and must be a finite
    /// integer.
    pub fn shift<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberShift(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Rotates the digits of `lhs` by `rhs`, storing the result in `lhs`.
    ///
    /// If `rhs` is positive, rotates to the left. If `rhs` is negative, rotates
    /// to the right.
    ///
    /// `rhs` specifies the number of positions to rotate, and must be a finite
    /// integer.
    pub fn rotate<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberRotate(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Multiplies `x` by 10<sup>`y`</sup>, storing the result in `x`.
    pub fn scaleb<const M: usize>(&mut self, x: &mut Decimal<N>, y: &Decimal<M>) {
        unsafe {
            decnumber_sys::decNumberScaleB(x.as_mut_ptr(), x.as_ptr(), y.as_ptr(), &mut self.inner);
        }
    }

    /// Computes the square root of `n`, storing the result in `n`.
    pub fn sqrt<const M: usize>(&mut self, n: &mut Decimal<M>) {
        let n = n.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberSquareRoot(n, n, &mut self.inner);
        }
    }

    /// Subtracts `rhs` from `lhs`, storing the result in `lhs`.
    pub fn sub<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberSubtract(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Sums all elements of `iter`.
    pub fn sum<'a, I, const M: usize>(&mut self, iter: I) -> Decimal<N>
    where
        I: Iterator<Item = &'a Decimal<M>>,
    {
        iter.fold(Decimal::<N>::zero(), |mut sum, d| {
            self.add(&mut sum, d);
            sum
        })
    }

    /// Determines the ordering of `lhs` relative to `rhs`, using the
    /// total order predicate defined in IEEE 754-2008.
    ///
    /// For a brief description of the ordering, consult [`f32::total_cmp`].
    pub fn total_cmp<const L: usize, const M: usize>(
        &mut self,
        lhs: &Decimal<L>,
        rhs: &Decimal<M>,
    ) -> Ordering {
        validate_n(N);
        let mut d = Decimal::<N>::zero();
        unsafe {
            decnumber_sys::decNumberCompareTotal(
                d.as_mut_ptr() as *mut decnumber_sys::decNumber,
                lhs.as_ptr(),
                rhs.as_ptr(),
                &mut self.inner,
            )
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
    pub fn xor<const M: usize>(&mut self, lhs: &mut Decimal<N>, rhs: &Decimal<M>) {
        let lhs = lhs.as_mut_ptr();
        unsafe {
            decnumber_sys::decNumberXor(lhs, lhs, rhs.as_ptr(), &mut self.inner);
        }
    }

    /// Returns `m` cast as a `Decimal::<N>`.
    ///
    /// `Context` uses similar statuses to arithmetic to express under- and
    /// overflow for values whose total precisions exceeds this context's.
    pub fn to_width<const M: usize>(&mut self, m: Decimal<M>) -> Decimal<N> {
        let mut n = Decimal::<N>::zero();
        unsafe {
            decnumber_sys::decNumberPlus(n.as_mut_ptr(), m.as_ptr(), &mut self.inner);
        }
        n
    }
}

#[cfg(feature = "num-traits")]
impl<const N: usize> Zero for Decimal<N> {
    #[inline]
    fn zero() -> Self {
        Decimal::<N>::zero()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.is_zero()
    }
}

#[cfg(feature = "num-traits")]
impl<const N: usize, const L: usize, const M: usize> MulAdd<Decimal<L>, Decimal<M>> for Decimal<N> {
    type Output = Self;

    #[inline]
    fn mul_add(mut self, a: Decimal<L>, b: Decimal<M>) -> Self::Output {
        self.mul_add_assign(a, b);
        self
    }
}

#[cfg(feature = "num-traits")]
impl<const N: usize, const L: usize, const M: usize> MulAddAssign<Decimal<L>, Decimal<M>>
    for Decimal<N>
{
    fn mul_add_assign(&mut self, a: Decimal<L>, b: Decimal<M>) {
        Context::<Self>::default().fma(self, &a, &b);
    }
}

#[cfg(feature = "num-traits")]
impl<const N: usize, const M: usize> Pow<Decimal<M>> for Decimal<N> {
    type Output = Self;

    fn pow(mut self, rhs: Decimal<M>) -> Self::Output {
        Context::<Decimal<N>>::default().pow(&mut self, &rhs);

        self
    }
}

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

use std::ffi::{CStr, CString};
use std::fmt;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::str::FromStr;

use libc::c_char;

use crate::context::Context;
#[cfg(feature = "arbitrary-precision")]
use crate::decimal::Decimal;
use crate::decimal64::Decimal64;
use crate::error::ParseDecimalError;

/// A 32-bit decimal floating-point number.
#[derive(Clone, Copy, Hash)]
pub struct Decimal32 {
    pub(crate) inner: decnumber_sys::decSingle,
}

impl Decimal32 {
    /// Constructs a 128-bit decimal floating-point number representing the
    /// number 0.
    pub fn zero() -> Decimal32 {
        Decimal32::default()
    }

    /// Creates a number from its representation as a little-endian byte array.
    pub fn from_le_bytes(mut bytes: [u8; 4]) -> Decimal32 {
        if cfg!(target_endian = "big") {
            bytes.reverse();
        }
        Decimal32::from_ne_bytes(bytes)
    }

    /// Creates a number from its representation as a big-endian byte array.
    pub fn from_be_bytes(mut bytes: [u8; 4]) -> Decimal32 {
        if cfg!(target_endian = "little") {
            bytes.reverse();
        }
        Decimal32::from_ne_bytes(bytes)
    }

    /// Creates a number from its representation as a byte array in the
    /// native endianness of the target platform.
    pub fn from_ne_bytes(bytes: [u8; 4]) -> Decimal32 {
        Decimal32 {
            inner: decnumber_sys::decSingle { bytes },
        }
    }

    /// Returns the memory representation of the number as a byte array in
    /// little-endian order.
    pub fn to_le_bytes(&self) -> [u8; 4] {
        let mut bytes = self.to_ne_bytes();
        if cfg!(target_endian = "big") {
            bytes.reverse();
        }
        bytes
    }

    /// Returns the memory representation of the number as a byte array in
    /// big-endian order.
    pub fn to_be_bytes(&self) -> [u8; 4] {
        let mut bytes = self.to_ne_bytes();
        if cfg!(target_endian = "little") {
            bytes.reverse();
        }
        bytes
    }

    /// Returns the memory representation of the number as a byte array in
    /// the native endianness of the target platform.
    pub fn to_ne_bytes(&self) -> [u8; 4] {
        self.inner.bytes
    }

    /// Computes the exponent of the number.
    pub fn exponent(&self) -> i32 {
        unsafe { decnumber_sys::decSingleGetExponent(&self.inner) }
    }
}

impl Default for Decimal32 {
    fn default() -> Decimal32 {
        let mut d = MaybeUninit::<decnumber_sys::decSingle>::uninit();
        let d = unsafe {
            decnumber_sys::decSingleZero(d.as_mut_ptr());
            d.assume_init()
        };
        Decimal32 { inner: d }
    }
}

impl fmt::Debug for Decimal32 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Decimal32 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buf = MaybeUninit::<[c_char; decnumber_sys::DECDOUBLE_String]>::uninit();
        let c_str = unsafe {
            if f.alternate() {
                decnumber_sys::decSingleToEngString(&self.inner, buf.as_mut_ptr() as *mut c_char);
            } else {
                decnumber_sys::decSingleToString(&self.inner, buf.as_mut_ptr() as *mut c_char);
            }
            CStr::from_ptr(buf.as_ptr() as *const c_char)
        };
        f.write_str(
            c_str
                .to_str()
                .expect("decSingleToString yields valid UTF-8"),
        )
    }
}

impl FromStr for Decimal32 {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Decimal32, ParseDecimalError> {
        Context::<Decimal32>::default().parse(s)
    }
}

impl Default for Context<Decimal32> {
    fn default() -> Context<Decimal32> {
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

impl Context<Decimal32> {
    /// Parses a number from its string representation.
    pub fn parse<S>(&mut self, s: S) -> Result<Decimal32, ParseDecimalError>
    where
        S: Into<Vec<u8>>,
    {
        let c_string = CString::new(s).map_err(|_| ParseDecimalError)?;
        let mut d = MaybeUninit::<decnumber_sys::decSingle>::uninit();
        let d = unsafe {
            decnumber_sys::decSingleFromString(d.as_mut_ptr(), c_string.as_ptr(), &mut self.inner);
            d.assume_init()
        };
        if (self.inner.status & decnumber_sys::DEC_Conversion_syntax) != 0 {
            Err(ParseDecimalError)
        } else {
            Ok(Decimal32 { inner: d })
        }
    }

    /// Constructs a number from a 64-bit decimal float.
    ///
    /// The result may be inexact. The status fields on the context will be set
    /// appropriately if so.
    pub fn from_decimal64(&mut self, d64: Decimal64) -> Decimal32 {
        let mut d32 = MaybeUninit::<decnumber_sys::decSingle>::uninit();
        let d32 = unsafe {
            decnumber_sys::decSingleFromWider(d32.as_mut_ptr(), &d64.inner, &mut self.inner);
            d32.assume_init()
        };
        Decimal32 { inner: d32 }
    }

    /// Constructs a number from an arbitrary-precision decimal.
    ///
    /// The result may be inexact. The status fields on the context will be set
    /// appropriately if so.
    #[cfg(feature = "arbitrary-precision")]
    pub fn from_decimal<const N: usize>(&mut self, d: &Decimal<N>) -> Decimal32 {
        let mut d32 = MaybeUninit::<decnumber_sys::decSingle>::uninit();
        let d32 = unsafe {
            decnumber_sys::decimal32FromNumber(d32.as_mut_ptr(), d.as_ptr(), &mut self.inner);
            d32.assume_init()
        };
        Decimal32 { inner: d32 }
    }
}
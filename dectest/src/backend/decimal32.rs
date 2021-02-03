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
// limitations under the License

use std::cmp::Ordering;
use std::hash::Hasher;
use std::str::FromStr;

use dec::{Class, Context, Decimal128, Decimal32, Decimal64, Rounding, Status};

use crate::backend::{Backend, BackendError, BackendResult};

pub struct Decimal32Backend {
    cx: Context<Decimal32>,
}

impl Backend for Decimal32Backend {
    type D = Decimal32;

    const HASHABLE: bool = false;
    const REPORTS_STATUS_CLAMPED: bool = false;
    const REPORTS_STATUS_ROUNDED: bool = false;
    const REPORTS_STATUS_SUBNORMAL: bool = false;

    fn new() -> Decimal32Backend {
        Decimal32Backend {
            cx: Context::default(),
        }
    }

    fn nan() -> Self::D {
        Self::D::from_str("NaN").unwrap()
    }

    fn parse(&mut self, s: &str, _precise: bool) -> Self::D {
        match self.cx.parse(s) {
            Ok(d) => d,
            Err(_) => Self::nan(),
        }
    }

    fn from_decimal32(&mut self, n: Decimal32) -> Self::D {
        n
    }

    fn from_decimal64(&mut self, n: Decimal64) -> Self::D {
        self.cx.from_decimal64(n)
    }

    fn from_decimal128(&mut self, n: Decimal128) -> Self::D {
        let d64 = Context::<Decimal64>::default().from_decimal128(n);
        self.from_decimal64(d64)
    }

    fn to_decimal32(&mut self, n: &Self::D) -> Decimal32 {
        *n
    }

    fn to_decimal64(&mut self, n: &Self::D) -> Decimal64 {
        Decimal64::from(*n)
    }

    fn to_decimal128(&mut self, n: &Self::D) -> Decimal128 {
        Decimal128::from(*n)
    }

    fn hash<H>(_: &Self::D, _: &mut H)
    where
        H: Hasher,
    {
        unimplemented!("Decimal32 does not implement Hash")
    }

    fn status(&self) -> Status {
        self.cx.status()
    }

    fn clear_status(&mut self) {
        self.cx.clear_status()
    }

    fn set_clamp(&mut self, clamp: bool) -> BackendResult<()> {
        match clamp {
            false => Err(BackendError::Unsupported),
            true => Ok(()),
        }
    }

    fn set_extended(&mut self, extended: bool) -> BackendResult<()> {
        match extended {
            false => Err(BackendError::Unsupported),
            true => Ok(()),
        }
    }

    fn set_max_exponent(&mut self, _: isize) -> BackendResult<()> {
        Ok(())
    }

    fn set_min_exponent(&mut self, _: isize) -> BackendResult<()> {
        Ok(())
    }

    fn set_precision(&mut self, p: usize) -> BackendResult<()> {
        match p {
            7 => Ok(()),
            _ => Err(BackendError::Unsupported),
        }
    }

    fn set_rounding(&mut self, rounding: Rounding) -> BackendResult<()> {
        self.cx.set_rounding(rounding);
        Ok(())
    }

    fn is_valid(&self, _: &str) -> bool {
        true
    }

    fn abs(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn add(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn and(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn canonical(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn class(&mut self, _: Self::D) -> Result<Class, BackendError> {
        Err(BackendError::Unsupported)
    }

    fn div(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn div_integer(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn exp(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn fma(&mut self, _: Self::D, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn invert(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn ln(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn log10(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn logb(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn max(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn max_abs(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn min(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn min_abs(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn minus(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn mul(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn next_minus(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn next_plus(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn next_toward(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn or(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn partial_cmp(&mut self, _: Self::D, _: Self::D) -> BackendResult<Option<Ordering>> {
        Err(BackendError::Unsupported)
    }

    fn plus(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn pow(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn quantize(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn quantum_matches(&mut self, _: Self::D, _: Self::D) -> BackendResult<bool> {
        Err(BackendError::Unsupported)
    }

    fn reduce(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn rem(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn rem_near(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn rotate(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn round(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn scaleb(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn shift(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn sqrt(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn sub(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn total_cmp(&mut self, _: Self::D, _: Self::D) -> BackendResult<Ordering> {
        Err(BackendError::Unsupported)
    }

    fn xor(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }
}

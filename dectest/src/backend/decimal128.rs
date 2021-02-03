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
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use dec::{Class, Context, Decimal128, Decimal32, Decimal64, Rounding, Status};

use crate::backend::{Backend, BackendError, BackendResult};

pub struct Decimal128Backend {
    cx: Context<Decimal128>,
}

impl Backend for Decimal128Backend {
    type D = Decimal128;

    const HASHABLE: bool = true;
    const REPORTS_STATUS_CLAMPED: bool = false;
    const REPORTS_STATUS_ROUNDED: bool = false;
    const REPORTS_STATUS_SUBNORMAL: bool = false;

    fn new() -> Decimal128Backend {
        Decimal128Backend {
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
        n.into()
    }

    fn from_decimal64(&mut self, n: Decimal64) -> Self::D {
        n.into()
    }

    fn from_decimal128(&mut self, n: Decimal128) -> Self::D {
        n
    }

    fn to_decimal32(&mut self, n: &Self::D) -> Decimal32 {
        let d64 = Context::<Decimal64>::default().from_decimal128(*n);
        Context::<Decimal32>::default().from_decimal64(d64)
    }

    fn to_decimal64(&mut self, n: &Self::D) -> Decimal64 {
        Context::<Decimal64>::default().from_decimal128(*n)
    }

    fn to_decimal128(&mut self, n: &Self::D) -> Decimal128 {
        *n
    }

    fn hash<H>(n: &Self::D, state: &mut H)
    where
        H: Hasher,
    {
        n.hash(state)
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
            34 => Ok(()),
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

    fn abs(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.abs(n))
    }

    fn add(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.add(lhs, rhs))
    }

    fn and(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.and(lhs, rhs))
    }

    fn canonical(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(n.canonical())
    }

    fn class(&mut self, n: Self::D) -> Result<Class, BackendError> {
        Ok(n.class())
    }

    fn div(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.div(lhs, rhs))
    }

    fn div_integer(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.div_integer(lhs, rhs))
    }

    fn exp(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn fma(&mut self, x: Self::D, y: Self::D, z: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.fma(x, y, z))
    }

    fn invert(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.invert(n))
    }

    fn ln(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn log10(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn logb(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.logb(n))
    }

    fn max(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.max(lhs, rhs))
    }

    fn max_abs(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.max_abs(lhs, rhs))
    }

    fn min(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.min(lhs, rhs))
    }

    fn min_abs(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.min_abs(lhs, rhs))
    }

    fn minus(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.minus(n))
    }

    fn mul(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.mul(lhs, rhs))
    }

    fn next_minus(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.next_minus(n))
    }

    fn next_plus(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.next_plus(n))
    }

    fn next_toward(&mut self, x: Self::D, y: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.next_toward(x, y))
    }

    fn or(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.or(lhs, rhs))
    }

    fn partial_cmp(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Option<Ordering>> {
        Ok(self.cx.partial_cmp(lhs, rhs))
    }

    fn plus(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.plus(n))
    }

    fn pow(&mut self, _: Self::D, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn quantize(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.quantize(lhs, rhs))
    }

    fn quantum_matches(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<bool> {
        Ok(lhs.quantum_matches(&rhs))
    }

    fn reduce(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.reduce(n))
    }

    fn rem(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.rem(lhs, rhs))
    }

    fn rem_near(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.rem_near(lhs, rhs))
    }

    fn rotate(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.rotate(lhs, rhs))
    }

    fn round(&mut self, n: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.round(n))
    }

    fn scaleb(&mut self, x: Self::D, y: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.scaleb(x, y))
    }

    fn shift(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.shift(lhs, rhs))
    }

    fn sqrt(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn sub(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.sub(lhs, rhs))
    }

    fn total_cmp(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Ordering> {
        Ok(lhs.total_cmp(&rhs))
    }

    fn xor(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        Ok(self.cx.xor(lhs, rhs))
    }
}

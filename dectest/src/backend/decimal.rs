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

use dec::{Class, Context, Decimal, Decimal128, Decimal32, Decimal64, Rounding, Status};

use crate::backend::{Backend, BackendError, BackendResult};

const N: usize = 300;

pub struct DecimalBackend {
    cx: Context<Decimal<N>>,
    valid: bool,
}

impl Backend for DecimalBackend {
    type D = Decimal<N>;

    const HASHABLE: bool = false;
    const REPORTS_STATUS_CLAMPED: bool = true;
    const REPORTS_STATUS_ROUNDED: bool = true;
    const REPORTS_STATUS_SUBNORMAL: bool = true;

    fn new() -> DecimalBackend {
        DecimalBackend {
            cx: Context::default(),
            valid: true,
        }
    }

    fn nan() -> Self::D {
        Decimal::<N>::from_str("NaN").unwrap()
    }

    fn parse(&mut self, s: &str, precise: bool) -> Self::D {
        let precision = self.cx.precision();
        if precise {
            self.cx.set_precision(N * 3).unwrap();
        }
        let res = match self.cx.parse(s) {
            Ok(d) => d,
            Err(_) => Self::nan(),
        };
        self.cx.set_precision(precision).unwrap();
        res
    }

    fn from_decimal32(&mut self, n: Decimal32) -> Self::D {
        n.into()
    }

    fn from_decimal64(&mut self, n: Decimal64) -> Self::D {
        n.into()
    }

    fn from_decimal128(&mut self, n: Decimal128) -> Self::D {
        n.into()
    }

    fn to_decimal32(&mut self, n: &Self::D) -> Decimal32 {
        n.to_decimal32()
    }

    fn to_decimal64(&mut self, n: &Self::D) -> Decimal64 {
        n.to_decimal64()
    }

    fn to_decimal128(&mut self, n: &Self::D) -> Decimal128 {
        n.to_decimal128()
    }

    fn hash<H>(_: &Self::D, _: &mut H)
    where
        H: Hasher,
    {
        unimplemented!("Decimal does not implement Hash")
    }

    fn status(&self) -> Status {
        self.cx.status()
    }

    fn clear_status(&mut self) {
        self.cx.clear_status()
    }

    fn set_clamp(&mut self, clamp: bool) -> BackendResult<()> {
        self.cx.set_clamp(clamp);
        Ok(())
    }

    fn set_extended(&mut self, extended: bool) -> BackendResult<()> {
        match extended {
            false => Err(BackendError::Unsupported),
            true => Ok(()),
        }
    }

    fn set_max_exponent(&mut self, e: isize) -> BackendResult<()> {
        self.cx
            .set_max_exponent(e)
            .map_err(|_| BackendError::Unsupported)
    }

    fn set_min_exponent(&mut self, e: isize) -> BackendResult<()> {
        self.cx
            .set_min_exponent(e)
            .map_err(|_| BackendError::Unsupported)
    }

    fn set_precision(&mut self, p: usize) -> BackendResult<()> {
        self.valid = self.cx.set_precision(p).is_ok();
        Ok(())
    }

    fn set_rounding(&mut self, rounding: Rounding) -> BackendResult<()> {
        self.cx.set_rounding(rounding);
        Ok(())
    }

    fn is_valid(&self, id: &str) -> bool {
        match id {
            // Failures documented in the test cases.
            "powx4302" | "powx4303" | "powx4342" | "powx4343" => false,
            // Other observed failures.
            "powx603" | "powx606" | "pwsx821" | "lnx116" | "lnx732" | "sqtx8643" | "sqtx9031"
            | "sqtx9032" | "sqtx9033" | "sqtx9034" | "sqtx9035" | "sqtx9036" | "sqtx9037"
            | "sqtx9038" | "sqtx9039" | "sqtx9040" | "sqtx9045" | "quax1026" => false,
            _ => self.valid,
        }
    }

    fn abs(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.abs(&mut n);
        Ok(n)
    }

    fn add(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.add(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn and(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.and(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn canonical(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn class(&mut self, n: Self::D) -> Result<Class, BackendError> {
        Ok(self.cx.class(&n))
    }

    fn div(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.div(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn div_integer(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.div_integer(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn exp(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.exp(&mut n);
        Ok(n)
    }

    fn fma(&mut self, mut x: Self::D, y: Self::D, z: Self::D) -> BackendResult<Self::D> {
        self.cx.fma(&mut x, &y, &z);
        Ok(x)
    }

    fn invert(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.invert(&mut n);
        Ok(n)
    }

    fn ln(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.ln(&mut n);
        Ok(n)
    }

    fn log10(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.log10(&mut n);
        Ok(n)
    }

    fn logb(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.logb(&mut n);
        Ok(n)
    }

    fn max(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.max(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn max_abs(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.max_abs(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn min(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.min(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn min_abs(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.min_abs(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn minus(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.minus(&mut n);
        Ok(n)
    }

    fn mul(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.mul(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn next_minus(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.next_minus(&mut n);
        Ok(n)
    }

    fn next_plus(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.next_plus(&mut n);
        Ok(n)
    }

    fn next_toward(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.next_toward(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn or(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.or(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn partial_cmp(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Option<Ordering>> {
        Ok(self.cx.partial_cmp(&lhs, &rhs))
    }

    fn plus(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.plus(&mut n);
        Ok(n)
    }

    fn pow(&mut self, mut x: Self::D, y: Self::D) -> BackendResult<Self::D> {
        self.cx.pow(&mut x, &y);
        Ok(x)
    }

    fn quantize(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.quantize(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn quantum_matches(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<bool> {
        Ok(lhs.quantum_matches(&rhs))
    }

    fn reduce(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.reduce(&mut n);
        Ok(n)
    }

    fn rem(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.rem(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn rem_near(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.rem_near(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn rotate(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.rotate(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn round(&mut self, _: Self::D) -> BackendResult<Self::D> {
        Err(BackendError::Unsupported)
    }

    fn scaleb(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.scaleb(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn shift(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.shift(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn sqrt(&mut self, mut n: Self::D) -> BackendResult<Self::D> {
        self.cx.sqrt(&mut n);
        Ok(n)
    }

    fn sub(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.sub(&mut lhs, &rhs);
        Ok(lhs)
    }

    fn total_cmp(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Ordering> {
        Ok(self.cx.total_cmp(&lhs, &rhs))
    }

    fn xor(&mut self, mut lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D> {
        self.cx.xor(&mut lhs, &rhs);
        Ok(lhs)
    }
}

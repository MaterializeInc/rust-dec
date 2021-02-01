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
use std::error::Error;
use std::fmt;

use dec::{Class, Decimal128, Decimal32, Decimal64, Rounding, Status};

#[cfg(feature = "arbitrary-precision")]
mod decimal;
mod decimal128;
mod decimal32;
mod decimal64;

#[cfg(feature = "arbitrary-precision")]
pub use decimal::DecimalBackend;
pub use decimal128::Decimal128Backend;
pub use decimal32::Decimal32Backend;
pub use decimal64::Decimal64Backend;

pub enum BackendError {
    Unsupported,
    Failure { cause: Box<dyn Error> },
}

impl BackendError {
    pub fn failure<S>(message: S) -> BackendError
    where
        S: Into<String>,
    {
        let message = message.into();
        BackendError::Failure {
            cause: message.into(),
        }
    }
}

impl<E> From<E> for BackendError
where
    E: Error + 'static,
{
    fn from(cause: E) -> BackendError {
        BackendError::Failure {
            cause: cause.into(),
        }
    }
}

pub type BackendResult<T> = Result<T, BackendError>;

pub trait Backend {
    type D: fmt::Display + Clone;

    const REPORTS_STATUS_CLAMPED: bool;
    const REPORTS_STATUS_ROUNDED: bool;
    const REPORTS_STATUS_SUBNORMAL: bool;

    fn new() -> Self;

    fn nan() -> Self::D;
    fn parse(&mut self, s: &str, precise: bool) -> Self::D;
    fn from_decimal32(&mut self, n: Decimal32) -> Self::D;
    fn from_decimal64(&mut self, n: Decimal64) -> Self::D;
    fn from_decimal128(&mut self, n: Decimal128) -> Self::D;
    fn to_decimal32(&mut self, n: &Self::D) -> Decimal32;
    fn to_decimal64(&mut self, n: &Self::D) -> Decimal64;
    fn to_decimal128(&mut self, n: &Self::D) -> Decimal128;

    fn status(&self) -> Status;
    fn clear_status(&mut self);
    fn set_clamp(&mut self, clamp: bool) -> BackendResult<()>;
    fn set_extended(&mut self, extended: bool) -> BackendResult<()>;
    fn set_max_exponent(&mut self, e: isize) -> BackendResult<()>;
    fn set_min_exponent(&mut self, e: isize) -> BackendResult<()>;
    fn set_precision(&mut self, p: usize) -> BackendResult<()>;
    fn set_rounding(&mut self, rounding: Rounding) -> BackendResult<()>;
    fn is_valid(&self, id: &str) -> bool;

    fn abs(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn add(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn and(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn canonical(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn class(&mut self, n: Self::D) -> Result<Class, BackendError>;
    fn div(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn div_integer(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn exp(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn fma(&mut self, x: Self::D, y: Self::D, z: Self::D) -> BackendResult<Self::D>;
    fn ln(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn log10(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn logb(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn max(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn max_abs(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn min(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn min_abs(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn minus(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn mul(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn next_minus(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn next_plus(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn next_toward(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn invert(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn or(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn partial_cmp(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Option<Ordering>>;
    fn plus(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn pow(&mut self, x: Self::D, y: Self::D) -> BackendResult<Self::D>;
    fn quantize(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn quantum_matches(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<bool>;
    fn reduce(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn rem(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn rem_near(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn rotate(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn round(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn scaleb(&mut self, x: Self::D, y: Self::D) -> BackendResult<Self::D>;
    fn shift(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn sqrt(&mut self, n: Self::D) -> BackendResult<Self::D>;
    fn sub(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
    fn total_cmp(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Ordering>;
    fn xor(&mut self, lhs: Self::D, rhs: Self::D) -> BackendResult<Self::D>;
}

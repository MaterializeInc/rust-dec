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
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::context::Context;
use crate::decimal128::Decimal128;
use crate::decimal64::Decimal64;

/// A wrapper for a decimal number that provides an implementation of [`Ord`]
/// and [`Hash`].
///
/// Like the [`OrderedFloat`] type provided by the [`ordered_float`] crate, but
/// for decimals.
///
/// NaN is treated as equal to itself and greater than all non-NaN values. All
/// other values are compared via their `PartialOrd` implementation.
///
/// At the moment `OrderedDecimal` can only wrap [`Decimal64`] and
/// [`Decimal128`]. Support for [`Decimal32`](crate::Decimal32) is not planned,
/// but support for [`Decimal<N>`](crate::Decimal) would be welcomed, provided a
/// suitable implementation can be found.
///
/// Note that the order used by `OrderedDecimal` is *not* the same as the order
/// used by the [`total_cmp`](Decimal64::total_cmp) method. The `total_cmp`
/// method takes exponents into account and therefore does not consider e.g.
/// `1.2` and `1.20` to be equal.
///
/// [`OrderedFloat`]: https://docs.rs/ordered-float/2.0.1/ordered_float/struct.OrderedFloat.html
/// [`ordered_float`]: https://crates.io/crates/ordered-float
#[derive(Debug, Clone, Copy)]
pub struct OrderedDecimal<D>(pub D);

impl<D> OrderedDecimal<D> {
    /// Consumes the ordered decimal wrapper, returning the decimal within.
    pub fn into_inner(self) -> D {
        self.0
    }
}

impl<D> fmt::Display for OrderedDecimal<D>
where
    D: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<D> PartialOrd for OrderedDecimal<D>
where
    Self: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<D> PartialEq for OrderedDecimal<D>
where
    Self: Ord,
{
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<D> Eq for OrderedDecimal<D> where Self: Ord {}

impl Ord for OrderedDecimal<Decimal64> {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut cx = Context::<Decimal64>::default();
        let lhs = cx.reduce(self.0);
        let rhs = cx.reduce(other.0);
        match cx.partial_cmp(lhs, rhs) {
            Some(ordering) => ordering,
            None => {
                if lhs.is_nan() {
                    if rhs.is_nan() {
                        Ordering::Equal
                    } else {
                        Ordering::Greater
                    }
                } else {
                    Ordering::Less
                }
            }
        }
    }
}

impl Hash for OrderedDecimal<Decimal64> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        let d = if self.0.is_nan() {
            Decimal64::NAN
        } else if self.0.is_zero() {
            Decimal64::ZERO
        } else {
            Context::<Decimal64>::default().reduce(self.0)
        };
        d.inner.bytes.hash(state)
    }
}

impl Ord for OrderedDecimal<Decimal128> {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut cx = Context::<Decimal128>::default();
        let lhs = cx.reduce(self.0);
        let rhs = cx.reduce(other.0);
        match cx.partial_cmp(lhs, rhs) {
            Some(ordering) => ordering,
            None => {
                if lhs.is_nan() {
                    if rhs.is_nan() {
                        Ordering::Equal
                    } else {
                        Ordering::Greater
                    }
                } else {
                    Ordering::Less
                }
            }
        }
    }
}

impl Hash for OrderedDecimal<Decimal128> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        let d = if self.0.is_nan() {
            Decimal128::NAN
        } else if self.0.is_zero() {
            Decimal128::ZERO
        } else {
            Context::<Decimal128>::default().reduce(self.0)
        };
        d.inner.bytes.hash(state)
    }
}

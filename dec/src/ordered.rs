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
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::str::FromStr;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::context::Context;
use crate::decimal::Decimal;
use crate::decimal128::Decimal128;
use crate::decimal32::Decimal32;
use crate::decimal64::Decimal64;
use crate::error::ParseDecimalError;

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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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

impl<const N: usize> Ord for OrderedDecimal<Decimal<N>> {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut cx = Context::<Decimal<N>>::default();
        let mut lhs = self.0.clone();
        let mut rhs = other.0.clone();
        cx.reduce(&mut lhs);
        cx.reduce(&mut rhs);
        match cx.partial_cmp(&lhs, &rhs) {
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

impl<const N: usize> Hash for OrderedDecimal<Decimal<N>> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        let d = if self.0.is_nan() {
            Decimal::<N>::nan()
        } else if self.0.is_infinite() {
            let mut d = Decimal::<N>::infinity();
            if self.0.is_negative() {
                Context::<Decimal<N>>::default().minus(&mut d);
            }
            d
        } else if self.0.is_zero() {
            Decimal::<N>::zero()
        } else {
            let mut d = self.0.clone();
            Context::<Decimal<N>>::default().reduce(&mut d);
            d
        };
        d.digits.hash(state);
        d.exponent.hash(state);
        d.bits.hash(state);
        d.coefficient_units().hash(state);
    }
}

impl<D> Default for OrderedDecimal<D>
where
    D: Default,
{
    fn default() -> Self {
        OrderedDecimal(D::default())
    }
}

impl<D> FromStr for OrderedDecimal<D>
where
    D: FromStr<Err = ParseDecimalError>,
{
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<OrderedDecimal<D>, ParseDecimalError> {
        Ok(OrderedDecimal(D::from_str(s)?))
    }
}

impl<D> From<i32> for OrderedDecimal<D>
where
    D: From<i32>,
{
    fn from(n: i32) -> OrderedDecimal<D> {
        OrderedDecimal(D::from(n))
    }
}

impl<D> From<u32> for OrderedDecimal<D>
where
    D: From<u32>,
{
    fn from(n: u32) -> OrderedDecimal<D> {
        OrderedDecimal(D::from(n))
    }
}

impl<D> From<Decimal32> for OrderedDecimal<D>
where
    D: From<Decimal32>,
{
    fn from(n: Decimal32) -> OrderedDecimal<D> {
        OrderedDecimal(D::from(n))
    }
}

impl<D> From<Decimal64> for OrderedDecimal<D>
where
    D: From<Decimal64>,
{
    fn from(n: Decimal64) -> OrderedDecimal<D> {
        OrderedDecimal(D::from(n))
    }
}

impl<D> From<Decimal128> for OrderedDecimal<D>
where
    D: From<Decimal128>,
{
    fn from(n: Decimal128) -> OrderedDecimal<D> {
        OrderedDecimal(D::from(n))
    }
}

impl<D> Add for OrderedDecimal<D>
where
    D: Add<Output = D>,
{
    type Output = Self;

    fn add(self, other: OrderedDecimal<D>) -> Self {
        OrderedDecimal(self.0 + other.0)
    }
}

impl<D> Add<D> for OrderedDecimal<D>
where
    D: Add<Output = D>,
{
    type Output = Self;

    fn add(self, other: D) -> Self {
        OrderedDecimal(self.0 + other)
    }
}

impl Add<OrderedDecimal<Decimal64>> for Decimal64 {
    type Output = Self;

    fn add(self, other: OrderedDecimal<Decimal64>) -> Self {
        self + other.0
    }
}

impl Add<OrderedDecimal<Decimal128>> for Decimal128 {
    type Output = Self;

    fn add(self, other: OrderedDecimal<Decimal128>) -> Self {
        self + other.0
    }
}

impl<D> AddAssign for OrderedDecimal<D>
where
    D: AddAssign,
{
    fn add_assign(&mut self, other: Self) {
        self.0 += other.0;
    }
}

/// Adds inner directly.
impl<D> AddAssign<D> for OrderedDecimal<D>
where
    D: Add<Output = D> + Copy,
{
    fn add_assign(&mut self, other: D) {
        *self = *self + other;
    }
}

impl<D> Sub for OrderedDecimal<D>
where
    D: Sub<Output = D>,
{
    type Output = Self;

    fn sub(self, other: OrderedDecimal<D>) -> Self {
        OrderedDecimal(self.0 - other.0)
    }
}

impl<D> Sub<D> for OrderedDecimal<D>
where
    D: Sub<Output = D>,
{
    type Output = Self;

    fn sub(self, other: D) -> Self {
        OrderedDecimal(self.0 - other)
    }
}

impl Sub<OrderedDecimal<Decimal64>> for Decimal64 {
    type Output = Self;

    fn sub(self, other: OrderedDecimal<Decimal64>) -> Self {
        self - other.0
    }
}

impl Sub<OrderedDecimal<Decimal128>> for Decimal128 {
    type Output = Self;

    fn sub(self, other: OrderedDecimal<Decimal128>) -> Self {
        self - other.0
    }
}

impl<D> SubAssign for OrderedDecimal<D>
where
    D: SubAssign,
{
    fn sub_assign(&mut self, other: Self) {
        self.0 -= other.0;
    }
}

/// Subs inner directly.
impl<D> SubAssign<D> for OrderedDecimal<D>
where
    D: Sub<Output = D> + Copy,
{
    fn sub_assign(&mut self, other: D) {
        *self = *self - other;
    }
}
impl<D> Mul for OrderedDecimal<D>
where
    D: Mul<Output = D>,
{
    type Output = Self;

    fn mul(self, other: OrderedDecimal<D>) -> Self {
        OrderedDecimal(self.0 * other.0)
    }
}

impl<D> Mul<D> for OrderedDecimal<D>
where
    D: Mul<Output = D>,
{
    type Output = Self;

    fn mul(self, other: D) -> Self {
        OrderedDecimal(self.0 * other)
    }
}

impl Mul<OrderedDecimal<Decimal64>> for Decimal64 {
    type Output = Self;

    fn mul(self, other: OrderedDecimal<Decimal64>) -> Self {
        self * other.0
    }
}

impl Mul<OrderedDecimal<Decimal128>> for Decimal128 {
    type Output = Self;

    fn mul(self, other: OrderedDecimal<Decimal128>) -> Self {
        self * other.0
    }
}

impl<D> MulAssign for OrderedDecimal<D>
where
    D: MulAssign,
{
    fn mul_assign(&mut self, other: Self) {
        self.0 *= other.0;
    }
}

/// Muls inner directly.
impl<D> MulAssign<D> for OrderedDecimal<D>
where
    D: Mul<Output = D> + Copy,
{
    fn mul_assign(&mut self, other: D) {
        *self = *self * other;
    }
}

impl<D> Div for OrderedDecimal<D>
where
    D: Div<Output = D>,
{
    type Output = Self;

    fn div(self, other: OrderedDecimal<D>) -> Self {
        OrderedDecimal(self.0 / other.0)
    }
}

impl<D> Div<D> for OrderedDecimal<D>
where
    D: Div<Output = D>,
{
    type Output = Self;

    fn div(self, other: D) -> Self {
        OrderedDecimal(self.0 / other)
    }
}

impl Div<OrderedDecimal<Decimal64>> for Decimal64 {
    type Output = Self;

    fn div(self, other: OrderedDecimal<Decimal64>) -> Self {
        self / other.0
    }
}

impl Div<OrderedDecimal<Decimal128>> for Decimal128 {
    type Output = Self;

    fn div(self, other: OrderedDecimal<Decimal128>) -> Self {
        self / other.0
    }
}

impl<D> DivAssign for OrderedDecimal<D>
where
    D: DivAssign,
{
    fn div_assign(&mut self, other: Self) {
        self.0 /= other.0;
    }
}

/// Divs inner directly.
impl<D> DivAssign<D> for OrderedDecimal<D>
where
    D: Div<Output = D> + Copy,
{
    fn div_assign(&mut self, other: D) {
        *self = *self / other;
    }
}

impl<D> Rem for OrderedDecimal<D>
where
    D: Rem<Output = D>,
{
    type Output = Self;

    fn rem(self, other: OrderedDecimal<D>) -> Self {
        OrderedDecimal(self.0 % other.0)
    }
}

impl<D> Rem<D> for OrderedDecimal<D>
where
    D: Rem<Output = D>,
{
    type Output = Self;

    fn rem(self, other: D) -> Self {
        OrderedDecimal(self.0 % other)
    }
}

impl Rem<OrderedDecimal<Decimal64>> for Decimal64 {
    type Output = Self;

    fn rem(self, other: OrderedDecimal<Decimal64>) -> Self {
        self % other.0
    }
}

impl Rem<OrderedDecimal<Decimal128>> for Decimal128 {
    type Output = Self;

    fn rem(self, other: OrderedDecimal<Decimal128>) -> Self {
        self % other.0
    }
}

impl<D> RemAssign for OrderedDecimal<D>
where
    D: RemAssign,
{
    fn rem_assign(&mut self, other: Self) {
        self.0 %= other.0;
    }
}

/// Rems inner directly.
impl<D> RemAssign<D> for OrderedDecimal<D>
where
    D: Rem<Output = D> + Copy,
{
    fn rem_assign(&mut self, other: D) {
        *self = *self % other;
    }
}

impl<D> Neg for OrderedDecimal<D>
where
    D: Neg<Output = D>,
{
    type Output = Self;

    fn neg(self) -> Self {
        OrderedDecimal(-self.0)
    }
}

impl<D> Sum for OrderedDecimal<D>
where
    D: Sum,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = OrderedDecimal<D>>,
    {
        OrderedDecimal(iter.map(|v| v.0).sum())
    }
}

impl<'a, D> Sum<&'a OrderedDecimal<D>> for OrderedDecimal<D>
where
    D: Sum<&'a D> + 'a,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a OrderedDecimal<D>>,
    {
        OrderedDecimal(iter.map(|v| &v.0).sum())
    }
}

impl<D> Product for OrderedDecimal<D>
where
    D: Product,
{
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = OrderedDecimal<D>>,
    {
        OrderedDecimal(iter.map(|v| v.0).product())
    }
}

impl<'a, D> Product<&'a OrderedDecimal<D>> for OrderedDecimal<D>
where
    D: Product<&'a D> + 'a,
{
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a OrderedDecimal<D>>,
    {
        OrderedDecimal(iter.map(|v| &v.0).product())
    }
}

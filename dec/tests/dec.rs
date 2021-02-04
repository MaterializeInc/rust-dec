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
use std::hash::{Hash, Hasher};
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

use dec::{Decimal128, Decimal32, Decimal64, OrderedDecimal};

#[derive(Default)]
struct ValidatingHasher {
    bytes: Vec<u8>,
}

impl Hasher for ValidatingHasher {
    fn write(&mut self, bytes: &[u8]) {
        self.bytes.extend(bytes)
    }

    fn finish(&self) -> u64 {
        unimplemented!()
    }
}

fn hash_data<H>(h: H) -> Vec<u8>
where
    H: Hash,
{
    let mut hasher = ValidatingHasher::default();
    h.hash(&mut hasher);
    hasher.bytes
}

const TESTS: &[(&str, &str, Ordering)] = &[
    ("1.2", "1.2", Ordering::Equal),
    ("1.2", "1.200", Ordering::Equal),
    ("1", "2", Ordering::Less),
    ("2", "1", Ordering::Greater),
    ("1", "NaN", Ordering::Less),
    ("NaN", "1", Ordering::Greater),
    ("Inf", "NaN", Ordering::Less),
    ("NaN", "Inf", Ordering::Greater),
    ("-Inf", "NaN", Ordering::Less),
    ("NaN", "-Inf", Ordering::Greater),
    ("NaN", "NaN", Ordering::Equal),
    ("sNaN", "NaN", Ordering::Equal),
    ("NaN42", "NaN21", Ordering::Equal),
    ("-0", "+0", Ordering::Equal),
];

#[test]
fn test_ordered_decimal64() -> Result<(), Box<dyn Error>> {
    for (lhs, rhs, expected) in TESTS {
        println!("cmp({}, {}): expected {:?}", lhs, rhs, expected);
        let lhs: OrderedDecimal<Decimal64> = OrderedDecimal(lhs.parse()?);
        let rhs: OrderedDecimal<Decimal64> = OrderedDecimal(rhs.parse()?);
        assert_eq!(lhs.cmp(&rhs), *expected);

        if lhs == rhs && hash_data(lhs) != hash_data(rhs) {
            panic!("{} and {} are equal but hashes are not equal", lhs, rhs);
        } else if lhs != rhs && hash_data(lhs) == hash_data(rhs) {
            panic!("{} and {} are equal but hashes are equal", lhs, rhs);
        }
    }
    Ok(())
}

#[test]
fn test_ordered_decimal128() -> Result<(), Box<dyn Error>> {
    for (lhs, rhs, expected) in TESTS {
        println!("cmp({}, {}): expected {:?}", lhs, rhs, expected);
        let lhs: OrderedDecimal<Decimal128> = OrderedDecimal(lhs.parse()?);
        let rhs: OrderedDecimal<Decimal128> = OrderedDecimal(rhs.parse()?);
        assert_eq!(lhs.cmp(&rhs), *expected);

        if lhs == rhs && hash_data(lhs) != hash_data(rhs) {
            panic!("{} and {} are equal but hashes are not equal", lhs, rhs);
        } else if lhs != rhs && hash_data(lhs) == hash_data(rhs) {
            panic!("{} and {} are equal but hashes are equal", lhs, rhs);
        }
    }
    Ok(())
}

#[test]
fn test_constants_decimal32() -> Result<(), Box<dyn Error>> {
    assert_eq!(Decimal32::ZERO.to_string(), "0");
    assert_eq!(Decimal32::ONE.to_string(), "1");
    assert_eq!(Decimal32::NAN.to_string(), "NaN");
    Ok(())
}

#[test]
fn test_constants_decimal64() -> Result<(), Box<dyn Error>> {
    assert_eq!(Decimal64::ZERO.to_string(), "0");
    assert_eq!(Decimal64::ONE.to_string(), "1");
    assert_eq!(Decimal64::NAN.to_string(), "NaN");
    Ok(())
}

#[test]
fn test_constants_decimal128() -> Result<(), Box<dyn Error>> {
    assert_eq!(Decimal128::ZERO.to_string(), "0");
    assert_eq!(Decimal128::ONE.to_string(), "1");
    assert_eq!(Decimal128::NAN.to_string(), "NaN");
    Ok(())
}

#[test]
fn test_overloading() -> Result<(), Box<dyn Error>> {
    // The goal here is only to test that the traits are wired up correctly,
    // e.g., to protect against transcription errors. The correctness of the
    // actual arithmetic operations is checked extensively by dectest.

    fn inner<T1, T2>() -> Result<(), Box<dyn Error>>
    where
        T1: Neg<Output = T1>
            + Add<T2, Output = T1>
            + Sub<T2, Output = T1>
            + Mul<T2, Output = T1>
            + Div<T2, Output = T1>
            + Rem<T2, Output = T1>
            + AddAssign
            + SubAssign
            + MulAssign
            + DivAssign
            + RemAssign
            + Sum
            + for<'a> Sum<&'a T1>
            + Product
            + for<'a> Product<&'a T1>
            + Product
            + PartialEq
            + From<i32>
            + fmt::Debug,
        T2: From<i32>,
    {
        let t1 = |t| T1::from(t);
        let t2 = |t| T2::from(t);

        assert_eq!(-t1(1), t1(-1));
        assert_eq!(t1(1) + t2(2), t1(3));
        assert_eq!(t1(3) - t2(2), t1(1));
        assert_eq!(t1(2) * t2(3), t1(6));
        assert_eq!(t1(10) / t2(2), t1(5));
        assert_eq!(t1(10) % t2(3), t1(1));

        let mut x = t1(1);
        x += t1(2);
        assert_eq!(x, t1(3));

        let mut x = t1(3);
        x -= t1(2);
        assert_eq!(x, t1(1));

        let mut x = t1(2);
        x *= t1(3);
        assert_eq!(x, t1(6));

        let mut x = t1(10);
        x /= t1(2);
        assert_eq!(x, t1(5));

        let mut x = t1(10);
        x %= t1(3);
        assert_eq!(x, t1(1));

        assert_eq!([t1(2), t1(2), t1(3)].iter().sum::<T1>(), t1(7));
        assert_eq!(vec![t1(2), t1(2), t1(3)].into_iter().sum::<T1>(), t1(7));

        assert_eq!([t1(2), t1(2), t1(3)].iter().product::<T1>(), t1(12));
        assert_eq!(
            vec![t1(2), t1(2), t1(3)].into_iter().product::<T1>(),
            t1(12)
        );

        Ok(())
    }

    inner::<Decimal64, Decimal64>()?;
    inner::<Decimal128, Decimal128>()?;
    inner::<OrderedDecimal<Decimal64>, OrderedDecimal<Decimal64>>()?;
    inner::<OrderedDecimal<Decimal64>, Decimal64>()?;
    inner::<OrderedDecimal<Decimal128>, Decimal128>()?;
    inner::<Decimal64, OrderedDecimal<Decimal64>>()?;
    inner::<Decimal128, OrderedDecimal<Decimal128>>()?;

    Ok(())
}

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

use dec::{Context, Decimal128, Decimal32, Decimal64, OrderedDecimal};

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

const ORDERING_TESTS: &[(&str, &str, Ordering)] = &[
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
    for (lhs, rhs, expected) in ORDERING_TESTS {
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
    for (lhs, rhs, expected) in ORDERING_TESTS {
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

#[test]
fn test_i64_to_decimal128() -> Result<(), Box<dyn Error>> {
    for &t in &[
        0,
        1i64,
        -1i64,
        i64::MAX,
        i64::MIN,
        i64::MAX / 2,
        i64::MIN / 2,
    ] {
        assert_eq!(Decimal128::from(t).to_string(), t.to_string());
    }
    Ok(())
}

#[test]
fn test_u64_to_decimal128() -> Result<(), Box<dyn Error>> {
    for &t in &[0, 1u64, u64::MAX, u64::MIN, u64::MAX / 2, u64::MIN / 2] {
        assert_eq!(Decimal128::from(t).to_string(), t.to_string());
    }
    Ok(())
}

#[test]
fn test_i128_to_decimal128() -> Result<(), Box<dyn Error>> {
    for &(input, output, inexact) in &[
        (1i128, "1", false),
        (-1i128, "-1", false),
        (i128::from(i64::MAX), "9223372036854775807", false),
        (i128::from(i64::MIN), "-9223372036854775808", false),
        (i128::MAX, "1.701411834604692317316873037158841E+38", true),
        (i128::MIN, "-1.701411834604692317316873037158841E+38", true),
        // +34 places is exact.
        (
            i128::MAX / 100000,
            "1701411834604692317316873037158841",
            false,
        ),
        (
            9_999_999_999_999_999_999_999_999_999_999_999i128,
            "9999999999999999999999999999999999",
            false,
        ),
        // +35 places places can be inexact.
        (
            i128::MAX / 10000,
            "1.701411834604692317316873037158841E+34",
            true,
        ),
        // +35 places can be exact.
        (
            10_000_000_000_000_000_000_000_000_000_000_000i128,
            "1.000000000000000000000000000000000E+34",
            false,
        ),
        // -34 places is exact.
        (
            i128::MIN / 100000,
            "-1701411834604692317316873037158841",
            false,
        ),
        (
            -9_999_999_999_999_999_999_999_999_999_999_999i128,
            "-9999999999999999999999999999999999",
            false,
        ),
        // -35 places can be inexact.
        (
            i128::MIN / 10000,
            "-1.701411834604692317316873037158841E+34",
            true,
        ),
        // -35 places can be exact.
        (
            -10_000_000_000_000_000_000_000_000_000_000_000i128,
            "-1.000000000000000000000000000000000E+34",
            false,
        ),
    ] {
        let mut cx = Context::<Decimal128>::default();
        let d = cx.from_i128(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }
    Ok(())
}

#[test]
fn test_u128_to_decimal128() -> Result<(), Box<dyn Error>> {
    for &(input, output, exact) in &[
        (1u128, "1", false),
        (u128::MAX, "3.402823669209384634633746074317682E+38", true),
        (u128::MIN, "0", false),
        // 34 places is exact.
        (
            u128::MAX / 100000,
            "3402823669209384634633746074317682",
            false,
        ),
        (
            9_999_999_999_999_999_999_999_999_999_999_999u128,
            "9999999999999999999999999999999999",
            false,
        ),
        // 35 places can be exact.
        (
            10_000_000_000_000_000_000_000_000_000_000_000u128,
            "1.000000000000000000000000000000000E+34",
            false,
        ),
        // 35 places can be inexact.
        (
            10_000_000_000_000_000_000_000_000_000_000_001u128,
            "1.000000000000000000000000000000000E+34",
            true,
        ),
    ] {
        let mut cx = Context::<Decimal128>::default();
        let d = cx.from_u128(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), exact);
    }
    Ok(())
}

#[test]
fn test_i64_to_decimal64() -> Result<(), Box<dyn Error>> {
    for &(input, output, inexact) in &[
        (1i64, "1", false),
        (-1i64, "-1", false),
        (i64::MAX, "9.223372036854776E+18", true),
        (i64::MIN, "-9.223372036854776E+18", true),
        (i64::MAX / 2, "4.611686018427388E+18", true),
        (i64::MIN / 2, "-4.611686018427388E+18", true),
        // +16 places is exact.
        (i64::MAX / 1000, "9223372036854775", false),
        (9_999_999_999_999_999i64, "9999999999999999", false),
        // +17 places can be exact.
        (1_000_0000_000_000_000i64, "1.000000000000000E+16", false),
        // +17 places can be inexact.
        (i64::MAX / 100, "9.223372036854776E+16", true),
        // -15 places is exact.
        (i64::MIN / 10000, "-922337203685477", false),
        (-999_999_999_999_999i64, "-999999999999999", false),
        // -16 places can be exact.
        (i64::MIN / 1000, "-9223372036854775", false),
        // -16 places can be inexact.
        (-9_999_999_999_999_999i64, "-9999999999999997", true),
    ] {
        let mut cx = Context::<Decimal64>::default();
        let d = cx.from_i64(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }
    Ok(())
}

#[test]
fn test_u64_to_decimal64() -> Result<(), Box<dyn Error>> {
    for &(input, output, inexact) in &[
        (1u64, "1", false),
        (u64::MAX, "1.844674407370955E+19", true),
        (u64::MIN, "0", false),
        // 16 digits is exact.
        (u64::MAX / 10000, "1844674407370955", false),
        (9_999_999_999_999_999u64, "9999999999999999", false),
        // 17 digits can be exact.
        (10_000_000_000_000_000u64, "1.000000000000000E+16", false),
        // 17 digits can be inexact.
        (u64::MAX / 1000, "1.844674407370955E+16", true),
    ] {
        let mut cx = Context::<Decimal64>::default();
        let d = cx.from_u64(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }

    Ok(())
}

#[test]
fn test_decimal32_decomposition() -> Result<(), Box<dyn Error>> {
    fn inner(input: &str, coefficient: i32, exponent: i32) {
        let d: Decimal32 = input.parse().unwrap();
        assert_eq!(d.coefficient(), coefficient);
        assert_eq!(d.exponent(), exponent);
    }
    inner("0", 0, 0);
    inner("1", 1, 0);
    inner("-1", -1, 0);
    inner("4294967295", 4294967, 3);
    inner("-4294967295", -4294967, 3);
    inner("4294967", 4294967, 0);
    inner("-4294967", -4294967, 0);
    inner("42949.67295", 4294967, -2);
    inner("-42949.67295", -4294967, -2);
    inner(".4294967295", 4294967, -7);
    inner("-.4294967295", -4294967, -7);

    Ok(())
}

#[test]
fn test_decimal64_decomposition() -> Result<(), Box<dyn Error>> {
    fn inner(input: &str, coefficient: i64, exponent: i32) {
        let d: Decimal64 = input.parse().unwrap();
        assert_eq!(d.coefficient(), coefficient);
        assert_eq!(d.exponent(), exponent);
    }
    inner("0", 0, 0);
    inner("1", 1, 0);
    inner("-1", -1, 0);
    inner("18446744073709551615", 1844674407370955, 4);
    inner("-18446744073709551615", -1844674407370955, 4);
    inner("1844674407370955", 1844674407370955, 0);
    inner("-1844674407370955", -1844674407370955, 0);
    inner("18446744.07370955", 1844674407370955, -8);
    inner("-18446744.07370955", -1844674407370955, -8);
    inner(".1844674407370955", 1844674407370955, -16);
    inner("-.1844674407370955", -1844674407370955, -16);

    // Test some very large number.
    let mut cx = Context::<Decimal64>::default();
    let mut d = cx.from_u64(u64::MAX);
    for _ in 0..4 {
        d = cx.mul(d, d);
    }

    assert_eq!(d.coefficient(), 1797693134862317);
    assert_eq!(d.exponent(), 293);

    Ok(())
}

#[test]
fn test_decimal64_special_value_coefficient() -> Result<(), Box<dyn Error>> {
    let mut cx = Context::<Decimal64>::default();
    let mut d = cx.from_u64(u64::MAX);

    // Increase d until it is an infinite value
    while d.is_finite() {
        d = cx.mul(d, d);
    }

    // +Infinity
    assert!(d.is_positive());
    assert!(d.is_infinite());
    assert_eq!(d.coefficient(), 0);

    // -Infinity
    d = -d;
    assert!(!d.is_positive());
    assert!(d.is_infinite());
    assert_eq!(d.coefficient(), 0);

    // NaN
    assert_eq!(Decimal64::NAN.coefficient(), 0);

    Ok(())
}

#[test]
fn test_decimal128_decomposition() -> Result<(), Box<dyn Error>> {
    fn inner(input: &str, coefficient: i128, exponent: i32) {
        let d: Decimal128 = input.parse().unwrap();
        assert_eq!(d.coefficient(), coefficient);
        assert_eq!(d.exponent(), exponent);
    }

    inner("0", 0, 0);
    inner("1", 1, 0);
    inner("-1", -1, 0);
    inner(
        "340282366920938463463374607431768211455",
        3402823669209384634633746074317682,
        5,
    );
    inner(
        "-340282366920938463463374607431768211455",
        -3402823669209384634633746074317682,
        5,
    );
    inner(
        "3402823669209384634633746074317682",
        3402823669209384634633746074317682,
        0,
    );
    inner(
        "-3402823669209384634633746074317682",
        -3402823669209384634633746074317682,
        0,
    );
    inner(
        "3402823669209384.634633746074317682",
        3402823669209384634633746074317682,
        -18,
    );
    inner(
        "-3402823669209384.634633746074317682",
        -3402823669209384634633746074317682,
        -18,
    );
    inner(
        ".3402823669209384634633746074317682",
        3402823669209384634633746074317682,
        -34,
    );
    inner(
        "-.3402823669209384634633746074317682",
        -3402823669209384634633746074317682,
        -34,
    );

    // Test some very large number.
    let mut cx = Context::<Decimal128>::default();
    let mut d = cx.from_u128(u128::MAX);
    for _ in 0..7 {
        d = cx.mul(d, d);
    }

    assert_eq!(d.coefficient(), 1189731495357231765085759326627988);
    assert_eq!(d.exponent(), 4899);

    Ok(())
}

#[test]
fn test_decimal128_special_value_coefficient() -> Result<(), Box<dyn Error>> {
    let mut cx = Context::<Decimal128>::default();
    let mut d = cx.from_u128(u128::MAX);

    // Increase d until it is an infinite value
    while d.is_finite() {
        d = cx.mul(d, d);
    }

    // +Infinity
    assert!(d.is_positive());
    assert!(d.is_infinite());
    assert_eq!(d.coefficient(), 0);

    // -Infinity
    d = -d;
    assert!(!d.is_positive());
    assert!(d.is_infinite());
    assert_eq!(d.coefficient(), 0);

    // NaN
    assert_eq!(Decimal128::NAN.coefficient(), 0);

    Ok(())
}

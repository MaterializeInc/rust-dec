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
use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

use dec::{Context, Decimal, Decimal128, Decimal32, Decimal64, OrderedDecimal, Status};

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
    ("1.2", "1.2000000000000000000000", Ordering::Equal),
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
fn test_ordered_decimal() -> Result<(), Box<dyn Error>> {
    for (lhs, rhs, expected) in ORDERING_TESTS {
        println!("cmp({}, {}): expected {:?}", lhs, rhs, expected);
        let lhs: OrderedDecimal<Decimal<12>> = OrderedDecimal(lhs.parse()?);
        let rhs: OrderedDecimal<Decimal<12>> = OrderedDecimal(rhs.parse()?);
        assert_eq!(lhs.cmp(&rhs), *expected);

        if lhs == rhs && hash_data(&lhs) != hash_data(&rhs) {
            panic!("{} and {} are equal but hashes are not equal", lhs, rhs);
        } else if lhs != rhs && hash_data(&lhs) == hash_data(&rhs) {
            panic!("{} and {} are not equal but hashes are equal", lhs, rhs);
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
    inner::<Decimal<12>, Decimal<12>>()?;
    inner::<Decimal<15>, Decimal<12>>()?;
    inner::<Decimal<12>, Decimal<15>>()?;

    Ok(())
}

#[test]
fn test_i64_to_decimal() -> Result<(), Box<dyn Error>> {
    use dec::Decimal;
    const N: usize = 12;
    fn inner(i: i64) {
        assert_eq!(Decimal::<N>::from(i).to_string(), i.to_string());
    }

    inner(0);
    inner(1i64);
    inner(-1i64);
    inner(i64::MAX);
    inner(i64::MIN);
    inner(i64::MAX / 2);
    inner(i64::MIN / 2);

    Ok(())
}

#[test]
fn test_u64_to_decimal() -> Result<(), Box<dyn Error>> {
    use dec::Decimal;
    const N: usize = 12;
    fn inner(i: u64) {
        assert_eq!(Decimal::<N>::from(i).to_string(), i.to_string());
    }

    inner(0);
    inner(1u64);
    inner(u64::MAX);
    inner(u64::MIN);
    inner(u64::MAX / 2);
    inner(u64::MIN / 2);

    Ok(())
}

#[test]
fn test_i128_to_decimal() -> Result<(), Box<dyn Error>> {
    use dec::Decimal;
    const N: usize = 12;
    fn inner(input: i128, output: &str, inexact: bool) {
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.from_i128(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }

    inner(1i128, "1", false);
    inner(-1i128, "-1", false);
    inner(i128::from(i64::MAX), "9223372036854775807", false);
    inner(i128::from(i64::MIN), "-9223372036854775808", false);
    inner(i128::MAX, "1.70141183460469231731687303715884105E+38", true);
    inner(
        i128::MIN,
        "-1.70141183460469231731687303715884106E+38",
        true,
    );
    // +34 places is exact.
    inner(
        i128::MAX / 100000,
        "1701411834604692317316873037158841",
        false,
    );
    inner(
        9_999_999_999_999_999_999_999_999_999_999_999i128,
        "9999999999999999999999999999999999",
        false,
    );
    // +36 places places can be inexact.
    inner(
        i128::MAX / 100,
        "1.70141183460469231731687303715884106E+36",
        true,
    );
    // +36 places can be exact.
    inner(
        1_000_000_000_000_000_000_000_000_000_000_000_000i128,
        "1.00000000000000000000000000000000000E+36",
        false,
    );
    // -34 places is exact.
    inner(
        i128::MIN / 100000,
        "-1701411834604692317316873037158841",
        false,
    );
    inner(
        -9_999_999_999_999_999_999_999_999_999_999_999i128,
        "-9999999999999999999999999999999999",
        false,
    );
    // -36 places can be inexact.
    inner(
        i128::MIN / 100,
        "-1.70141183460469231731687303715884106E+36",
        true,
    );
    // -36 places can be exact.
    inner(
        -1_000_000_000_000_000_000_000_000_000_000_000_000i128,
        "-1.00000000000000000000000000000000000E+36",
        false,
    );
    Ok(())
}

#[test]
fn test_u128_to_decimal() -> Result<(), Box<dyn Error>> {
    use dec::Decimal;
    const N: usize = 12;
    fn inner(input: u128, output: &str, inexact: bool) {
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.from_u128(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }
    inner(1u128, "1", false);
    inner(u128::MAX, "3.40282366920938463463374607431768211E+38", true);
    inner(u128::MIN, "0", false);
    // 34 places is exact.
    inner(
        u128::MAX / 100000,
        "3402823669209384634633746074317682",
        false,
    );
    inner(
        9_999_999_999_999_999_999_999_999_999_999_999u128,
        "9999999999999999999999999999999999",
        false,
    );
    // 36 places can be exact.
    inner(
        1_000_000_000_000_000_000_000_000_000_000_000_000u128,
        "1.00000000000000000000000000000000000E+36",
        false,
    );
    // 36 places can be inexact.
    inner(
        1_000_000_000_000_000_000_000_000_000_000_000_001u128,
        "1.00000000000000000000000000000000000E+36",
        true,
    );
    Ok(())
}

#[test]
fn test_i64_to_decimal128() -> Result<(), Box<dyn Error>> {
    fn inner(i: i64) {
        assert_eq!(Decimal128::from(i).to_string(), i.to_string());
    }

    inner(0);
    inner(1i64);
    inner(-1i64);
    inner(i64::MAX);
    inner(i64::MIN);
    inner(i64::MAX / 2);
    inner(i64::MIN / 2);

    Ok(())
}

#[test]
fn test_u64_to_decimal128() -> Result<(), Box<dyn Error>> {
    fn inner(i: u64) {
        assert_eq!(Decimal128::from(i).to_string(), i.to_string());
    }

    inner(0);
    inner(1u64);
    inner(u64::MAX);
    inner(u64::MIN);
    inner(u64::MAX / 2);
    inner(u64::MIN / 2);

    Ok(())
}

#[test]
fn test_i128_to_decimal128() -> Result<(), Box<dyn Error>> {
    fn inner(input: i128, output: &str, inexact: bool) {
        let mut cx = Context::<Decimal128>::default();
        let d = cx.from_i128(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }

    inner(1i128, "1", false);
    inner(-1i128, "-1", false);
    inner(i128::from(i64::MAX), "9223372036854775807", false);
    inner(i128::from(i64::MIN), "-9223372036854775808", false);
    inner(i128::MAX, "1.701411834604692317316873037158841E+38", true);
    inner(i128::MIN, "-1.701411834604692317316873037158841E+38", true);
    // +34 places is exact.
    inner(
        i128::MAX / 100000,
        "1701411834604692317316873037158841",
        false,
    );
    inner(
        9_999_999_999_999_999_999_999_999_999_999_999i128,
        "9999999999999999999999999999999999",
        false,
    );
    // +35 places places can be inexact.
    inner(
        i128::MAX / 10000,
        "1.701411834604692317316873037158841E+34",
        true,
    );
    // +35 places can be exact.
    inner(
        10_000_000_000_000_000_000_000_000_000_000_000i128,
        "1.000000000000000000000000000000000E+34",
        false,
    );
    // -34 places is exact.
    inner(
        i128::MIN / 100000,
        "-1701411834604692317316873037158841",
        false,
    );
    inner(
        -9_999_999_999_999_999_999_999_999_999_999_999i128,
        "-9999999999999999999999999999999999",
        false,
    );
    // -35 places can be inexact.
    inner(
        i128::MIN / 10000,
        "-1.701411834604692317316873037158841E+34",
        true,
    );
    // -35 places can be exact.
    inner(
        -10_000_000_000_000_000_000_000_000_000_000_000i128,
        "-1.000000000000000000000000000000000E+34",
        false,
    );
    Ok(())
}

#[test]
fn test_u128_to_decimal128() -> Result<(), Box<dyn Error>> {
    fn inner(input: u128, output: &str, inexact: bool) {
        let mut cx = Context::<Decimal128>::default();
        let d = cx.from_u128(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }
    inner(1u128, "1", false);
    inner(u128::MAX, "3.402823669209384634633746074317682E+38", true);
    inner(u128::MIN, "0", false);
    // 34 places is exact.
    inner(
        u128::MAX / 100000,
        "3402823669209384634633746074317682",
        false,
    );
    inner(
        9_999_999_999_999_999_999_999_999_999_999_999u128,
        "9999999999999999999999999999999999",
        false,
    );
    // 35 places can be exact.
    inner(
        10_000_000_000_000_000_000_000_000_000_000_000u128,
        "1.000000000000000000000000000000000E+34",
        false,
    );
    // 35 places can be inexact.
    inner(
        10_000_000_000_000_000_000_000_000_000_000_001u128,
        "1.000000000000000000000000000000000E+34",
        true,
    );
    Ok(())
}

#[test]
fn test_i64_to_decimal64() -> Result<(), Box<dyn Error>> {
    fn inner(input: i64, output: &str, inexact: bool) {
        let mut cx = Context::<Decimal64>::default();
        let d = cx.from_i64(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }
    inner(1i64, "1", false);
    inner(-1i64, "-1", false);
    inner(i64::MAX, "9.223372036854776E+18", true);
    inner(i64::MIN, "-9.223372036854776E+18", true);
    inner(i64::MAX / 2, "4.611686018427388E+18", true);
    inner(i64::MIN / 2, "-4.611686018427388E+18", true);
    // +16 places is exact.
    inner(i64::MAX / 1000, "9223372036854775", false);
    inner(9_999_999_999_999_999i64, "9999999999999999", false);
    // +17 places can be exact.
    inner(1_000_0000_000_000_000i64, "1.000000000000000E+16", false);
    // +17 places can be inexact.
    inner(i64::MAX / 100, "9.223372036854776E+16", true);
    // -15 places is exact.
    inner(i64::MIN / 10000, "-922337203685477", false);
    inner(-999_999_999_999_999i64, "-999999999999999", false);
    // -16 places can be exact.
    inner(i64::MIN / 1000, "-9223372036854775", false);
    // -16 places can be inexact.
    inner(-9_999_999_999_999_999i64, "-9999999999999997", true);
    Ok(())
}

#[test]
fn test_u64_to_decimal64() -> Result<(), Box<dyn Error>> {
    fn inner(input: u64, output: &str, inexact: bool) {
        let mut cx = Context::<Decimal64>::default();
        let d = cx.from_u64(input).to_string();
        assert_eq!(d.to_string(), output);
        assert_eq!(cx.status().inexact(), inexact);
    }
    inner(1u64, "1", false);
    inner(u64::MAX, "1.844674407370955E+19", true);
    inner(u64::MIN, "0", false);
    // 16 digits is exact.
    inner(u64::MAX / 10000, "1844674407370955", false);
    inner(9_999_999_999_999_999u64, "9999999999999999", false);
    // 17 digits can be exact.
    inner(10_000_000_000_000_000u64, "1.000000000000000E+16", false);
    // 17 digits can be inexact.
    inner(u64::MAX / 1000, "1.844674407370955E+16", true);

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

#[test]
/// Light integration test of `Decimal128` operations.
fn test_decimal128_ops() -> Result<(), Box<dyn Error>> {
    let mut cx = Context::<Decimal128>::default();
    let d = cx.from_u128(u128::MAX);

    let mut e = cx.from_i128(d.coefficient());
    e = cx.scaleb(e, Decimal128::from(5));
    e = cx.sub(d, e);

    assert_eq!(cx.reduce(e), Decimal128::from(0));

    Ok(())
}

#[test]
/// Light integration test of `Decimal64` operations.
fn test_decimal64_ops() -> Result<(), Box<dyn Error>> {
    let mut cx = Context::<Decimal64>::default();
    let d = cx.from_u64(u64::MAX);

    let mut e = cx.from_i64(d.coefficient());
    e = cx.scaleb(e, Decimal64::from(4));
    e = cx.sub(d, e);

    assert_eq!(cx.reduce(e), Decimal64::from(0));

    Ok(())
}

#[test]
fn test_decimal64_set_exponent() -> Result<(), Box<dyn Error>> {
    let mut cx = Context::<Decimal64>::default();
    let d = Decimal64::from(3);
    let mut d = cx.div(d, Decimal64::from(2));

    assert_eq!(d.exponent(), -1);
    assert_eq!("1.5", d.to_string());

    cx.set_exponent(&mut d, -2);

    assert_eq!(d.exponent(), -2);
    assert_eq!("0.15", d.to_string());

    cx.set_exponent(&mut d, 0);
    let d = cx.reduce(d);

    assert_eq!(d.exponent(), 0);
    assert_eq!("15", d.to_string());

    Ok(())
}

#[test]
fn test_decimal128_set_exponent() -> Result<(), Box<dyn Error>> {
    let mut cx = Context::<Decimal128>::default();
    let d = Decimal128::from(3);
    let mut d = cx.div(d, Decimal128::from(2));

    assert_eq!(d.exponent(), -1);
    assert_eq!("1.5", d.to_string());

    cx.set_exponent(&mut d, -2);

    assert_eq!(d.exponent(), -2);
    assert_eq!("0.15", d.to_string());

    cx.set_exponent(&mut d, 0);
    let d = cx.reduce(d);

    assert_eq!(d.exponent(), 0);
    assert_eq!("15", d.to_string());

    Ok(())
}

#[test]
fn test_standard_notation_dec_64() {
    // Test output on summed numbers
    fn sum_inner(l: &str, r: &str) {
        let mut cx = Context::<Decimal128>::default();
        let l = cx.parse(l).unwrap();
        let r = cx.parse(r).unwrap();
        let s = l + r;
        assert_eq!(s.to_string(), s.to_standard_notation_string());
    }
    sum_inner("1.23", "2.34");
    sum_inner(".123", ".234");
    sum_inner("1.23", ".234");
    sum_inner("1.23", "234");
    sum_inner("1.23", ".77");
    sum_inner("10", "2");
    sum_inner("-1.23", "1.23");

    // Test output on a div that maxes out precision
    let mut cx = Context::<Decimal64>::default();
    let l = cx.parse("1.2103500000").unwrap();
    let r = Decimal64::ONE / l;
    assert_eq!("0.8262072954104185", r.to_standard_notation_string());

    fn inner(d: i64, tests: &[(i32, &str, &str)]) {
        let mut cx = Context::<Decimal64>::default();
        let mut d = cx.from_i64(d);

        for t in tests {
            cx.set_exponent(&mut d, t.0);
            assert_eq!(t.1, d.to_string());
            assert_eq!(
                t.2,
                d.to_standard_notation_string(),
                "{} should render {} as its standard notation string",
                d,
                t.2
            );
        }
    }

    // Test rescaling numbers
    // - Some large number
    inner(
        -123456789012345678,
        &[
            (5, "-1.234567890123457E+20", "-123456789012345700000"),
            (10, "-1.234567890123457E+25", "-12345678901234570000000000"),
            (-8, "-12345678.90123457", "-12345678.90123457"),
            (
                -25,
                "-1.234567890123457E-10",
                "-0.0000000001234567890123457",
            ),
        ],
    );

    // - Zero
    inner(
        0,
        &[
            (0, "0", "0"),
            (10, "0E+10", "0"),
            (
                -43,
                "0E-43",
                "0.0000000000000000000000000000000000000000000",
            ),
        ],
    );

    // - Intrinsic trailing zeroes
    inner(
        -1000000000000000,
        &[
            (5, "-1.000000000000000E+20", "-100000000000000000000"),
            (10, "-1.000000000000000E+25", "-10000000000000000000000000"),
            (-8, "-10000000.00000000", "-10000000.00000000"),
            (
                -25,
                "-1.000000000000000E-10",
                "-0.0000000001000000000000000",
            ),
        ],
    );

    fn special_value_inner(s: &str, f: fn(&Decimal64) -> bool) {
        let mut cx = Context::<Decimal64>::default();
        let d = cx.parse(s).unwrap();
        assert_eq!(d.to_string(), d.to_standard_notation_string());
        assert!(f(&d));
    }
    special_value_inner("NaN", Decimal64::is_nan);
    special_value_inner("Infinity", Decimal64::is_infinite);
    special_value_inner("-Infinity", Decimal64::is_infinite);
}

#[test]
fn test_standard_notation_dec_128() {
    // Test output on summed numbers
    fn sum_inner(l: &str, r: &str) {
        let mut cx = Context::<Decimal128>::default();
        let l = cx.parse(l).unwrap();
        let r = cx.parse(r).unwrap();
        let s = l + r;
        assert_eq!(s.to_string(), s.to_standard_notation_string());
    }
    sum_inner("1.23", "2.34");
    sum_inner(".123", ".234");
    sum_inner("1.23", ".234");
    sum_inner("1.23", "234");
    sum_inner("1.23", ".77");
    sum_inner("10", "2");
    sum_inner("-1.23", "1.23");

    // Test output on a div that maxes out precision
    let mut cx = Context::<Decimal128>::default();
    let d = cx.parse("1.21035").unwrap();

    let r = Decimal128::ONE / d;
    assert_eq!(
        "0.8262072954104184739951253769570785",
        r.to_standard_notation_string()
    );

    fn inner(d: i128, tests: &[(i32, &str, &str)]) {
        let mut cx = Context::<Decimal128>::default();
        let mut d = cx.from_i128(d);

        for t in tests {
            cx.set_exponent(&mut d, t.0);
            assert_eq!(t.1, d.to_string());
            assert_eq!(t.2, d.to_standard_notation_string());
        }
    }

    // Test rescaling numbers
    // - Some large number
    inner(
        -123456789012345678901234567890123456789,
        &[
            (
                5,
                "-1.234567890123456789012345678901234E+38",
                "-123456789012345678901234567890123400000",
            ),
            (
                10,
                "-1.234567890123456789012345678901234E+43",
                "-12345678901234567890123456789012340000000000",
            ),
            (
                -17,
                "-12345678901234567.89012345678901234",
                "-12345678901234567.89012345678901234",
            ),
            (
                -43,
                "-1.234567890123456789012345678901234E-10",
                "-0.0000000001234567890123456789012345678901234",
            ),
        ],
    );

    // - Zero
    inner(
        0,
        &[
            (0, "0", "0"),
            (10, "0E+10", "0"),
            (
                -43,
                "0E-43",
                "0.0000000000000000000000000000000000000000000",
            ),
        ],
    );

    // - Intrinsic trailing zeroes
    inner(
        -100000000000000000000000000000000000000,
        &[
            (
                5,
                "-1.000000000000000000000000000000000E+38",
                "-100000000000000000000000000000000000000",
            ),
            (
                10,
                "-1.000000000000000000000000000000000E+43",
                "-10000000000000000000000000000000000000000000",
            ),
            (
                -17,
                "-10000000000000000.00000000000000000",
                "-10000000000000000.00000000000000000",
            ),
            (
                -43,
                "-1.000000000000000000000000000000000E-10",
                "-0.0000000001000000000000000000000000000000000",
            ),
        ],
    );

    fn special_value_inner(s: &str, f: fn(&Decimal128) -> bool) {
        let mut cx = Context::<Decimal128>::default();
        let d = cx.parse(s).unwrap();
        assert_eq!(d.to_string(), d.to_standard_notation_string());
        assert!(f(&d));
    }
    special_value_inner("NaN", Decimal128::is_nan);
    special_value_inner("Infinity", Decimal128::is_infinite);
    special_value_inner("-Infinity", Decimal128::is_infinite);
}

#[test]
fn test_standard_notation_decimal() {
    const N: usize = 12;

    // Test output on summed numbers
    fn sum_inner(l: &str, r: &str) {
        let mut cx = Context::<Decimal<N>>::default();
        let mut l = cx.parse(l).unwrap();
        let r = cx.parse(r).unwrap();
        cx.add(&mut l, &r);
        assert_eq!(l.to_string(), l.to_standard_notation_string());
    }
    sum_inner("1.23", "2.34");
    sum_inner(".123", ".234");
    sum_inner("1.23", ".234");
    sum_inner("1.23", "234");
    sum_inner("1.23", ".77");
    sum_inner("10", "2");
    sum_inner("-1.23", "1.23");

    // Test output on a div that maxes out precision
    let mut cx = Context::<Decimal<N>>::default();
    let d = cx.parse("1.21035").unwrap();
    let mut r = cx.parse("1").unwrap();
    cx.div(&mut r, &d);

    assert_eq!(
        "0.826207295410418473995125376957078531",
        r.to_standard_notation_string()
    );

    fn special_value_inner(s: &str, f: fn(&Decimal<N>) -> bool) {
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.parse(s).unwrap();
        assert_eq!(d.to_string(), d.to_standard_notation_string());
        assert!(f(&d));
    }
    special_value_inner("NaN", Decimal::<N>::is_nan);
    special_value_inner("Infinity", Decimal::<N>::is_infinite);
    special_value_inner("-Infinity", Decimal::<N>::is_infinite);
}

#[test]
fn test_decimal64_rescale() -> Result<(), Box<dyn Error>> {
    let mut inexact_error = Status::default();
    inexact_error.set_inexact();
    let mut invalid_op_error = Status::default();
    invalid_op_error.set_invalid_operation();

    let new_cx = || Context::<Decimal64>::default();
    let mut cx = new_cx();
    let d = cx.div(Decimal64::from(22), Decimal64::from(7));
    let d_original = cx.scaleb(d, Decimal64::from(7));

    assert_eq!(d_original.exponent(), -8);
    assert_eq!(d_original.to_string(), "31428571.42857143");

    // 5 digits of scale
    let mut d = d_original;
    cx.rescale(&mut d, -5);
    // assert_eq!(d.exponent(), -5);
    assert_eq!(d.to_string(), "31428571.42857");
    // Context status reports inexact only when you drop some but not all
    // decimal values.
    assert!(cx.status() == inexact_error);

    // 0 digits of scale
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 0);
    assert_eq!(d.exponent(), 0);
    assert_eq!(d.to_string(), "31428571");
    assert!(!cx.status().any());

    // E+5
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 5);
    assert_eq!(d.exponent(), 5);
    assert_eq!(d.to_string(), "3.14E+7");
    assert!(!cx.status().any());

    // Invent zeroes when going from higher to lower scales
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 5);
    cx.rescale(&mut d, -5);
    assert_eq!(d.exponent(), -5);
    assert_eq!(d.to_string(), "31400000.00000");
    assert!(!cx.status().any());

    // Invalid operation when new exponent exceeds min/max exponent.
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 100);
    assert!(cx.status() == invalid_op_error);

    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, -100);
    assert!(cx.status() == invalid_op_error);

    Ok(())
}

#[test]
fn test_decimal128_rescale() -> Result<(), Box<dyn Error>> {
    let mut inexact_error = Status::default();
    inexact_error.set_inexact();
    let mut invalid_op_error = Status::default();
    invalid_op_error.set_invalid_operation();

    let new_cx = || Context::<Decimal128>::default();
    let mut cx = new_cx();
    let d = cx.div(Decimal128::from(22), Decimal128::from(7));
    let d_original = cx.scaleb(d, Decimal128::from(7));

    assert_eq!(d_original.exponent(), -26);
    assert_eq!(
        d_original.to_string(),
        "31428571.42857142857142857142857143"
    );

    // 5 digits of scale
    let mut d = d_original;
    cx.rescale(&mut d, -5);
    assert_eq!(d.exponent(), -5);
    assert_eq!(d.to_string(), "31428571.42857");
    // Context status reports inexact only when you drop some but not all
    // decimal values.
    assert!(cx.status() == inexact_error);

    // 0 digits of scale
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 0);
    assert_eq!(d.exponent(), 0);
    assert_eq!(d.to_string(), "31428571");
    assert!(!cx.status().any());

    // E+5
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 5);
    assert_eq!(d.exponent(), 5);
    assert_eq!(d.to_string(), "3.14E+7");
    assert!(!cx.status().any());

    // Invent zeroes when going from higher to lower scales
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 5);
    cx.rescale(&mut d, -5);
    assert_eq!(d.exponent(), -5);
    assert_eq!(d.to_string(), "31400000.00000");
    assert!(!cx.status().any());

    // Invalid operation when new exponent exceeds min/max exponent.
    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, 100);
    assert!(cx.status() == invalid_op_error);

    let mut d = d_original;
    let mut cx = new_cx();
    cx.rescale(&mut d, -100);
    assert!(cx.status() == invalid_op_error);

    Ok(())
}

#[test]
fn test_to_width_decimal() {
    use crate::Status;
    const N: usize = 12;
    const W: usize = N + 1;
    fn wide_to_narrow(v: &str, s: &str, digits: u32, exponent: i32, statuses: &[fn(&mut Status)]) {
        let mut cx_n = Context::<dec::Decimal<N>>::default();
        let mut cx_w = Context::<dec::Decimal<W>>::default();
        let v_w = cx_w.parse(v).unwrap();
        let v_n = cx_n.to_width(v_w);
        assert_eq!(v_n.to_string(), s);
        assert_eq!(v_n.digits(), digits);
        assert_eq!(v_n.exponent(), exponent);
        let mut status = Status::default();
        for set_status in statuses {
            set_status(&mut status);
        }
        assert_eq!(cx_n.status(), status);
    }
    // Coefficient fits, exp fits
    wide_to_narrow("1.23E+10", "1.23E+10", 3, 8, &[]);
    wide_to_narrow("1.23E-10", "1.23E-10", 3, -12, &[]);
    // Coefficient fits, exp "exceeds" precision, which has no effect
    wide_to_narrow("1.23E+40", "1.23E+40", 3, 38, &[]);
    // Coefficient doesn't fit
    wide_to_narrow(
        "9876543210123456789012345678901234567",
        "9.87654321012345678901234567890123457E+36",
        36,
        1,
        &[Status::set_inexact, Status::set_rounded],
    );
    wide_to_narrow(
        "9.87654321012345678901234567890123456789E-10",
        "9.87654321012345678901234567890123457E-10",
        36,
        -45,
        &[Status::set_inexact, Status::set_rounded],
    );
    wide_to_narrow("Infinity", "Infinity", 1, 0, &[]);

    fn narrow_to_wide(v: &str, s: &str, digits: u32, exponent: i32) {
        let mut cx_n = Context::<dec::Decimal<N>>::default();
        let mut cx_w = Context::<dec::Decimal<W>>::default();
        let v_n = cx_n.parse(v).unwrap();
        let v_w = cx_w.to_width(v_n);
        assert_eq!(v_w.to_string(), s);
        assert_eq!(v_w.digits(), digits);
        assert_eq!(v_w.exponent(), exponent);
        assert!(!cx_n.status().any());
    }
    // Coefficient fits, exp fits
    narrow_to_wide("1.23E+10", "1.23E+10", 3, 8);
    narrow_to_wide(
        "9.87654321012345678901234567890123457E+36",
        "9.87654321012345678901234567890123457E+36",
        36,
        1,
    );
    narrow_to_wide("Infinity", "Infinity", 1, 0);

    fn min_max_exp_wide_to_narrow(
        v: &str,
        s: &str,
        digits: u32,
        exponent: i32,
        statuses: &[fn(&mut Status)],
    ) {
        let mut cx_n = Context::<dec::Decimal<N>>::default();
        cx_n.set_max_exponent(N as isize * 3 - 1).unwrap();
        cx_n.set_min_exponent(-(N as isize) * 3 + 1).unwrap();
        let mut cx_w = Context::<dec::Decimal<W>>::default();
        let v_w = cx_w.parse(v).unwrap();
        let v_n = cx_n.to_width(v_w);
        assert_eq!(v_n.to_string(), s);
        assert_eq!(v_n.digits(), digits);
        assert_eq!(v_n.exponent(), exponent);
        let mut status = Status::default();
        for set_status in statuses {
            set_status(&mut status);
        }
        assert_eq!(cx_n.status(), status);
    }
    min_max_exp_wide_to_narrow(
        "98765432101234567890123456789012345",
        "98765432101234567890123456789012345",
        35,
        0,
        &[],
    );
    min_max_exp_wide_to_narrow("9E-10", "9E-10", 1, -10, &[]);
    // Exceeds max
    min_max_exp_wide_to_narrow(
        "9E37",
        "Infinity",
        1,
        0,
        &[
            Status::set_inexact,
            Status::set_overflow,
            Status::set_rounded,
        ],
    );
    // Exceeds min
    min_max_exp_wide_to_narrow("9E-36", "9E-36", 1, -36, &[Status::set_subnormal]);
    // ~= 9E-37
    min_max_exp_wide_to_narrow(
        ".0000000000000000000000000000000000009",
        "9E-37",
        1,
        -37,
        &[Status::set_subnormal],
    );
    min_max_exp_wide_to_narrow(
        ".12345678901234567890123456789012345678901234567890",
        "0.123456789012345678901234567890123457",
        36,
        -36,
        &[Status::set_inexact, Status::set_rounded],
    );
    min_max_exp_wide_to_narrow(
        "9E-100",
        "0E-70",
        1,
        -70,
        &[
            Status::set_clamped,
            Status::set_inexact,
            Status::set_rounded,
            Status::set_subnormal,
            Status::set_underflow,
        ],
    );
}

#[test]
/// Aggregate a set of valid values with width `N` into width `M`, and then go
/// back to `N`-width. This test is bespoke for Materialize's needs when
/// aggregating values using library.
fn test_agg_wide_narrow_decnum() {
    const N: usize = 12;
    const M: usize = N + 1;
    fn inner(
        v: &[&str],
        e_m: &str,
        statuses_m: &[fn(&mut Status)],
        e_n: &str,
        statuses_n: &[fn(&mut Status)],
    ) {
        let mut cx_n = Context::<dec::Decimal<N>>::default();
        // 35 max exp == 36 digits max
        cx_n.set_max_exponent(N as isize * 3 - 1).unwrap();
        let mut cx_m = Context::<dec::Decimal<M>>::default();
        // 36 max exp == 37 digits max
        cx_m.set_max_exponent(M as isize * 3 - 3).unwrap();

        // Parse values as `N`, but then convert to `M` and aggregate.
        let s = v
            .iter()
            .map(|v| {
                let v_n = cx_n.parse(*v).unwrap();
                cx_m.to_width(v_n)
            })
            .collect::<Vec<_>>();

        // Aggregate.
        let sum_m = cx_m.sum(s.iter());
        assert_eq!(sum_m.to_string(), e_m);

        let mut status = Status::default();
        for set_status in statuses_m {
            set_status(&mut status);
        }
        assert_eq!(cx_m.status(), status);

        // Go back to `N`.
        let sum_n = cx_n.to_width(sum_m.clone());

        assert_eq!(sum_n.to_string(), e_n);

        let mut status = Status::default();
        for set_status in statuses_n {
            set_status(&mut status);
        }
        assert_eq!(cx_n.status(), status);
    }
    // Vanilla aggregation
    inner(
        &["9876543210", "123456789"],
        "9999999999",
        &[],
        "9999999999",
        &[],
    );
    // Ensure intermediate value exceeds `N`.
    inner(
        &[
            "987654321012345678901234567890123456",
            "987654321012345678901234567890123456",
        ],
        "1975308642024691357802469135780246912",
        &[],
        "Infinity",
        &[
            Status::set_inexact,
            Status::set_overflow,
            Status::set_rounded,
        ],
    );
    inner(
        &["9e35", "9e35"],
        "1800000000000000000000000000000000000",
        &[],
        "Infinity",
        &[
            Status::set_inexact,
            Status::set_overflow,
            Status::set_rounded,
        ],
    );
    // Ensure intermediate value exceeds `N`, negative.
    inner(
        &[
            "-987654321012345678901234567890123456",
            "-987654321012345678901234567890123456",
        ],
        "-1975308642024691357802469135780246912",
        &[],
        "-Infinity",
        &[
            Status::set_inexact,
            Status::set_overflow,
            Status::set_rounded,
        ],
    );
    // Test infinities
    inner(&["Infinity", "Infinity"], "Infinity", &[], "Infinity", &[]);
    inner(
        &["-Infinity", "Infinity"],
        "NaN",
        &[Status::set_invalid_operation],
        "NaN",
        &[],
    );
    // Span agg width OK
    inner(
        &["9e35", "9e-3"],
        "900000000000000000000000000000000000.009",
        &[],
        "900000000000000000000000000000000000",
        &[Status::set_inexact, Status::set_rounded],
    );
    // Exceed `M`'s width the hard way
    inner(
        &[
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35", "9e35",
            "9e35", "9e35", "9e35", "9e35",
        ],
        "Infinity",
        &[
            Status::set_inexact,
            Status::set_overflow,
            Status::set_rounded,
        ],
        "Infinity",
        // Because the wide value is infinity, the narrow value is, as well, but
        // it isn't intrinsically aware of the aggregate's inexactitude, meaning
        // its context does not propagate the status.
        &[],
    );
    // Exceed `M`'s width the easy way
    inner(
        &["9e35", "9e35", "9e-3"],
        "1800000000000000000000000000000000000.01",
        &[Status::set_inexact, Status::set_rounded],
        "Infinity",
        &[
            Status::set_inexact,
            Status::set_overflow,
            Status::set_rounded,
        ],
    );
}

#[test]
fn test_cx_into_i64() {
    fn inner(v: i64) {
        let mut cx = Context::<Decimal<13>>::default();
        let d = Decimal::<13>::from(v);
        assert_eq!(Ok(v), cx.try_into_i64(d));
    }

    inner(0);
    inner(1);
    inner(i64::MIN);
    inner(i64::MAX);
    inner(i64::MIN / 3);
    inner(i64::MAX / 3);
    inner(i64::MIN / 7);
    inner(i64::MAX / 7);
    inner(1627418240000);
}

#[test]
fn test_cx_into_u64() {
    fn inner(v: u64) {
        let mut cx = Context::<Decimal<13>>::default();
        let d = Decimal::<13>::from(v);
        assert_eq!(Ok(v), cx.try_into_u64(d));
    }
    inner(u64::MIN);
    inner(u64::MAX);
    inner(u64::MAX / 3);
    inner(u64::MAX / 7);
    inner(1627418240000);
}

#[test]
fn test_cx_into_i128() {
    fn inner(v: i128) {
        let mut cx = Context::<Decimal<13>>::default();
        let d = cx.from_i128(v);
        assert_eq!(Ok(v), cx.try_into_i128(d));
    }
    inner(i128::MIN);
    inner(i128::MAX);
    inner(i128::MIN / 3);
    inner(i128::MAX / 3);
    inner(i128::MIN / 7);
    inner(i128::MAX / 7);
    inner(1627418240000);
}

#[test]
fn test_cx_into_u128() {
    fn inner(v: u128) {
        let mut cx = Context::<Decimal<13>>::default();
        let d = cx.from_u128(v);
        assert_eq!(Ok(v), cx.try_into_u128(d));
    }

    inner(u128::MIN / 3);
    inner(u128::MAX / 3);
    inner(u128::MIN / 7);
    inner(u128::MAX / 7);
    inner(1627418240000);
}

#[test]
fn test_decnum_tryinto_primitive() {
    const WIDTH: usize = 14;
    let mut cx = Context::<Decimal<WIDTH>>::default();
    let min_u8 = Decimal::<WIDTH>::from(u8::MIN);
    let max_u8 = Decimal::<WIDTH>::from(u8::MAX);
    let min_i8 = Decimal::<WIDTH>::from(i8::MIN);
    let max_i8 = Decimal::<WIDTH>::from(i8::MAX);
    let min_u16 = Decimal::<WIDTH>::from(u16::MIN);
    let max_u16 = Decimal::<WIDTH>::from(u16::MAX);
    let min_i16 = Decimal::<WIDTH>::from(i16::MIN);
    let max_i16 = Decimal::<WIDTH>::from(i16::MAX);
    let min_u32 = Decimal::<WIDTH>::from(u32::MIN);
    let max_u32 = Decimal::<WIDTH>::from(u32::MAX);
    let min_i32 = Decimal::<WIDTH>::from(i32::MIN);
    let max_i32 = Decimal::<WIDTH>::from(i32::MAX);
    let min_u64 = Decimal::<WIDTH>::from(u64::MIN);
    let max_u64 = Decimal::<WIDTH>::from(u64::MAX);
    let min_i64 = Decimal::<WIDTH>::from(i64::MIN);
    let max_i64 = Decimal::<WIDTH>::from(i64::MAX);
    let min_u128 = cx.from_u128(u128::MIN);
    let max_u128 = cx.from_u128(u128::MAX);
    let min_i128 = cx.from_i128(i128::MIN);
    let max_i128 = cx.from_i128(i128::MAX);
    let trailing_zeroes_int = Decimal::<WIDTH>::from(1927418240000i64);
    let trailing_zeroes_frac = cx.parse("12345.000").unwrap();
    let scientific_notation = cx.parse("2E5").unwrap();

    let inner = |v: &Decimal<WIDTH>| {
        let i_u8 = u8::try_from(*v);
        let i_i8 = i8::try_from(*v);
        let i_u16 = u16::try_from(*v);
        let i_i16 = i16::try_from(*v);
        let i_u32 = u32::try_from(*v);
        let i_i32 = i32::try_from(*v);
        let i_u64 = u64::try_from(*v);
        let i_i64 = i64::try_from(*v);
        let i_u128 = u128::try_from(*v);
        let i_i128 = i128::try_from(*v);

        // u8
        if v >= &min_u8 && v <= &max_u8 {
            assert!(i_u8.is_ok());
        } else {
            assert!(i_u8.is_err());
        }

        // i8
        if v >= &min_i8 && v <= &max_i8 {
            assert!(i_i8.is_ok());
        } else {
            assert!(i_i8.is_err());
        }

        // u16
        if v >= &min_u16 && v <= &max_u16 {
            assert!(i_u16.is_ok());
        } else {
            assert!(i_u16.is_err());
        }

        // i16
        if v >= &min_i16 && v <= &max_i16 {
            assert!(i_i16.is_ok());
        } else {
            assert!(i_i16.is_err());
        }

        // u32
        if v >= &min_u32 && v <= &max_u32 {
            assert!(i_u32.is_ok());
        } else {
            assert!(i_u32.is_err());
        }

        // i32
        if v >= &min_i32 && v <= &max_i32 {
            assert!(i_i32.is_ok());
        } else {
            assert!(i_i32.is_err());
        }

        // u64
        if v >= &min_u64 && v <= &max_u64 {
            assert!(i_u64.is_ok());
        } else {
            assert!(i_u64.is_err());
        }

        // i64
        if v >= &min_i64 && v <= &max_i64 {
            assert!(i_i64.is_ok());
        } else {
            assert!(i_i64.is_err());
        }

        // u128
        if v >= &min_u128 && v <= &max_u128 {
            assert!(i_u128.is_ok());
        } else {
            assert!(i_u128.is_err());
        }

        // i128
        if v >= &min_i128 && v <= &max_i128 {
            assert!(i_i128.is_ok());
        } else {
            assert!(i_i128.is_err());
        }
    };

    inner(&min_u32);
    inner(&max_u32);
    inner(&min_i32);
    inner(&max_i32);
    inner(&min_u64);
    inner(&max_u64);
    inner(&min_i64);
    inner(&max_i64);
    inner(&min_u128);
    inner(&max_u128);
    inner(&min_i128);
    inner(&max_i128);
    inner(&trailing_zeroes_int);
    inner(&trailing_zeroes_frac);
    inner(&scientific_notation);

    fn inner_expect_failure(s: &str) {
        let mut cx = Context::<Decimal<WIDTH>>::default();
        let v = cx.parse(s).unwrap();
        assert!(u32::try_from(v).is_err());
        assert!(i32::try_from(v).is_err());
        assert!(u64::try_from(v).is_err());
        assert!(i64::try_from(v).is_err());
        assert!(u128::try_from(v).is_err());
        assert!(i128::try_from(v).is_err());
    }

    inner_expect_failure("1.2");
    inner_expect_failure("-1.2");
    inner_expect_failure("1E-2");
    inner_expect_failure("-1E-2");
    inner_expect_failure("2E-10");
    inner_expect_failure("Infinity");
    inner_expect_failure("-Infinity");
    inner_expect_failure("NaN");
    inner_expect_failure("123E41");
}

#[test]
fn test_decnum_tryinto_primitive_f32() {
    const WIDTH: usize = 14;
    fn inner(s: &str, e: Result<f32, ()>) {
        let mut cx = Context::<Decimal<WIDTH>>::default();
        let d = cx.parse(s).unwrap();
        let r = cx.try_into_f32(d);
        if e.is_err() {
            assert!(r.is_err(), "expected {:?}, got {:?}", e, r)
        } else {
            let e = e.unwrap();
            let r = r.unwrap();
            if e.is_nan() {
                assert!(r.is_nan())
            } else {
                assert_eq!(e, r)
            }
        }
    }
    inner("1.234", Ok(1.234));
    inner("1234.567891234567", Ok(1234.5679));
    inner(
        "0.0000000000000001234567891234567",
        Ok(0.00000000000000012345679),
    );
    inner(
        "-0.0000000000000001234567891234567",
        Ok(-0.00000000000000012345679),
    );
    inner("0.000", Ok(0.0));
    inner("NaN", Ok(f32::NAN));
    inner("-NaN", Ok(f32::NAN));
    inner("Infinity", Ok(f32::INFINITY));
    inner("-Infinity", Ok(f32::NEG_INFINITY));
    inner("1000", Ok(1000.0));
    inner(&f32::MAX.to_string(), Ok(f32::MAX));
    inner(&f32::MIN.to_string(), Ok(f32::MIN));
    inner(&f64::MAX.to_string(), Err(()));
    inner(&f64::MIN.to_string(), Err(()));
    inner("1e39", Err(()));
    inner("1e-50", Err(()));
}

#[test]
fn test_decnum_tryinto_primitive_f64() {
    const WIDTH: usize = 14;
    fn inner(s: &str, f: Result<f64, ()>) {
        let mut cx = Context::<Decimal<WIDTH>>::default();
        let d = cx.parse(s).unwrap();
        let r = cx.try_into_f64(d);

        if f.is_err() {
            assert!(r.is_err(), "expected {:?}, got {:?}", f, r)
        } else {
            let f = f.unwrap();
            let r = r.unwrap();
            if f.is_nan() {
                assert!(f.is_nan())
            } else {
                assert_eq!(f, r)
            }
        }
    }
    inner("1.234", Ok(1.234));
    inner(
        "1234567890.12345678901234567891234567890",
        Ok(1234567890.1234568),
    );
    inner(
        "12345678912345678901.234567891234567890",
        Ok(12345678912345680000.0),
    );
    inner(
        ".0000000000000000000000012345678912345678901234567891234567890",
        Ok(0.000000000000000000000001234567891234568),
    );
    inner(
        "1.2345678912345678901234567891234567890E-24",
        Ok(0.000000000000000000000001234567891234568),
    );
    inner(
        "-1.2345678912345678901234567891234567890E-24",
        Ok(-0.000000000000000000000001234567891234568),
    );
    inner("1e39", Ok(1000000000000000000000000000000000000000.0));
    inner("0.000", Ok(0.0));
    inner(&f64::MAX.to_string(), Ok(f64::MAX));
    inner(&f64::MIN.to_string(), Ok(f64::MIN));
    inner("NaN", Ok(f64::NAN));
    inner("-NaN", Ok(f64::NAN));
    inner("Infinity", Ok(f64::INFINITY));
    inner("-Infinity", Ok(f64::NEG_INFINITY));
    inner("1e500", Err(()));
    inner("1e-500", Err(()));
}

#[test]
fn test_decnum_try_from_f32() {
    const WIDTH: usize = 12;
    fn inner(f: f32, e: &str) {
        let mut cx = Context::<Decimal<WIDTH>>::default();
        let d = cx.from_f32(f);
        let e = cx.parse(e).unwrap();
        if e.is_nan() {
            assert!(d.is_nan());
        } else {
            assert_eq!(d, e);
        }
    }
    inner(0f32, "0");
    inner(0.0f32, "0");
    inner(1f32, "1");
    inner(101.101, "101.101");
    inner(-101.101, "-101.101");
    inner(f32::MAX, &f32::MAX.to_string());
    inner(f32::MIN, &f32::MIN.to_string());
    inner(f32::INFINITY, "infinity");
    inner(f32::NEG_INFINITY, "-infinity");
    inner(f32::NAN, "NaN");
    inner(1.2345e-45f32, "1E-45");
    inner(
        12345678901234567890123456789012345678f32,
        "1.23456780000000000000000000000000000E+37",
    );
}

#[test]
fn test_decnum_try_from_f64() {
    const WIDTH: usize = 12;
    fn inner(f: f64, e: &str) {
        println!("f {}", f);
        let mut cx = Context::<Decimal<WIDTH>>::default();
        let d = cx.from_f64(f);
        let e = cx.parse(e).unwrap();
        if e.is_nan() {
            assert!(d.is_nan());
        } else {
            assert_eq!(d, e);
        }
    }
    inner(0f64, "0");
    inner(0.0f64, "0");
    inner(1f64, "1");
    inner(101.101, "101.101");
    inner(-101.101, "-101.101");
    inner(f64::MAX, &f64::MAX.to_string());
    inner(f64::MIN, &f64::MIN.to_string());
    inner(f64::INFINITY, "infinity");
    inner(f64::NEG_INFINITY, "-infinity");
    inner(f64::NAN, "NaN");
    inner(1.2345e-45f64, "1.2345E-45");
    inner(
        12345678901234567890123456789012345678901234567890123456789012345678901234567890f64,
        "1.23456789012345680000000000000000000E+79",
    );
    inner(9.8765431E-300, "9.8765431E-300");
    inner(9.8765431E-400, "0");
    inner(9.8765431E305, "9.87654310000000000000000000000000000E+305");
}

#[test]
fn test_decnum_coefficient() {
    const WIDTH: usize = 14;
    let mut cx = Context::<Decimal<WIDTH>>::default();
    let min_u32 = Decimal::<WIDTH>::from(u32::MIN);
    let max_u32 = Decimal::<WIDTH>::from(u32::MAX);
    let min_i32 = Decimal::<WIDTH>::from(i32::MIN);
    let max_i32 = Decimal::<WIDTH>::from(i32::MAX);
    let min_u64 = Decimal::<WIDTH>::from(u64::MIN);
    let max_u64 = Decimal::<WIDTH>::from(u64::MAX);
    let min_i64 = Decimal::<WIDTH>::from(i64::MIN);
    let max_i64 = Decimal::<WIDTH>::from(i64::MAX);
    let min_u128 = cx.from_u128(u128::MIN);
    let max_u128 = cx.from_u128(u128::MAX);
    let min_i128 = cx.from_i128(i128::MIN);
    let max_i128 = cx.from_i128(i128::MAX);

    let inner = |v: &Decimal<WIDTH>| {
        let mut v = v.clone();
        let i_u32 = v.coefficient::<u32>();
        let i_i32 = v.coefficient::<i32>();
        let i_u64 = v.coefficient::<u64>();
        let i_i64 = v.coefficient::<i64>();
        let i_u128 = v.coefficient::<u128>();
        let i_i128 = v.coefficient::<i128>();

        // u32
        if v >= min_u32 && v <= max_u32 && !v.is_negative() {
            assert!(i_u32.is_ok());
        } else {
            assert!(i_u32.is_err());
        }

        // i32
        if v >= min_i32 && v <= max_i32 {
            assert!(i_i32.is_ok());
        } else {
            assert!(i_i32.is_err());
        }

        // u64
        if v >= min_u64 && v <= max_u64 && !v.is_negative() {
            assert!(i_u64.is_ok());
        } else {
            assert!(i_u64.is_err());
        }

        // i64
        if v >= min_i64 && v <= max_i64 {
            assert!(i_i64.is_ok());
        } else {
            assert!(i_i64.is_err());
        }

        // u128
        if v >= min_u128 && v <= max_u128 && !v.is_negative() {
            assert!(i_u128.is_ok());
        } else {
            assert!(i_u128.is_err());
        }

        // i128
        if v >= min_i128 && v <= max_i128 {
            assert!(i_i128.is_ok());
        } else {
            assert!(i_i128.is_err());
        }
    };

    inner(&min_u32);
    inner(&max_u32);
    inner(&min_i32);
    inner(&max_i32);
    inner(&min_u64);
    inner(&max_u64);
    inner(&min_i64);
    inner(&max_i64);
    inner(&min_u128);
    inner(&max_u128);
    inner(&min_i128);
    inner(&max_i128);
}

#[test]
fn decnum_raw_parts() {
    fn inner(s: &str, o: Option<i128>) {
        const N: usize = 13;
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.parse(s).unwrap();
        let (digits, exponent, bits, lsu) = d.to_raw_parts();
        let r = unsafe { Decimal::<N>::from_raw_parts(digits, exponent, bits, &lsu) };
        if d.is_nan() {
            assert!(r.is_nan())
        } else {
            assert_eq!(d, r);
        }
        if let Some(o) = o {
            let o = cx.from_i128(o);
            assert_eq!(o, d);
        }
    }
    inner("1", Some(1));
    inner("-1", Some(-1));
    inner("0.00", Some(0));
    inner("987654321", Some(987654321));
    inner("-987654321", Some(-987654321));
    inner(&i128::MAX.to_string(), Some(i128::MAX));
    inner(&i128::MIN.to_string(), Some(i128::MIN));
    inner("98765.4321", None);
    inner("-98765.4321", None);
    inner("Infinity", None);
    inner("-Infinity", None);
    inner("NaN", None);
}

#[test]
fn decnum_round_to_place() {
    fn inner(s: &str, expect: &[&str]) {
        const N: usize = 13;
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.parse(s).unwrap();
        for (i, expect) in expect.iter().enumerate() {
            let mut n = d.clone();
            cx.round_to_place(&mut n, i + 1)
                .expect("only valid test cases");
            assert_eq!(&n.to_string(), expect);
        }
    }
    inner("599.18", &["6E+2", "6.0E+2", "599", "599.2", "599.18"]);
    inner("99.19", &["1E+2", "99"]);
    inner("1009", &["1E+3", "1.0E+3", "1.01E+3", "1009"]);
}

#[test]
fn decnum_round_reduce_to_place() {
    fn inner(s: &str, expect: &[&str]) {
        const N: usize = 13;
        let mut cx = Context::<Decimal<N>>::default();
        let d = cx.parse(s).unwrap();
        for (i, expect) in expect.iter().enumerate() {
            let mut n = d.clone();
            cx.round_reduce_to_place(&mut n, i + 1)
                .expect("only valid test cases");
            assert_eq!(&n.to_string(), expect);
        }
    }
    inner("599.18", &["6E+2", "6E+2", "599", "599.2", "599.18"]);
    inner("1009", &["1E+3", "1E+3", "1.01E+3", "1009"]);
}

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
use std::hash::{Hash, Hasher};

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
    assert_eq!(Decimal32::NAN.to_string(), "NaN");
    Ok(())
}

#[test]
fn test_constants_decimal64() -> Result<(), Box<dyn Error>> {
    assert_eq!(Decimal64::ZERO.to_string(), "0");
    assert_eq!(Decimal64::NAN.to_string(), "NaN");
    Ok(())
}

#[test]
fn test_constants_decimal128() -> Result<(), Box<dyn Error>> {
    assert_eq!(Decimal128::ZERO.to_string(), "0");
    assert_eq!(Decimal128::NAN.to_string(), "NaN");
    Ok(())
}

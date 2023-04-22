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
use std::convert::TryFrom;
use std::str::FromStr;

use serde::{Deserialize, Serialize};
use serde_json::json;
use serde_test::{assert_tokens, Token};

use dec::{Context, Decimal};

#[test]
fn test_serde() {
    const N: usize = 12;
    let mut cx = Context::<dec::Decimal<N>>::default();
    let d = cx.parse("-12.34").unwrap();

    assert_tokens(
        &d,
        &[
            Token::Struct {
                name: "Decimal",
                len: 4,
            },
            Token::Str("digits"),
            Token::U32(4),
            Token::Str("exponent"),
            Token::I32(-2),
            Token::Str("bits"),
            // This is equal to decnumber_sys::DECNEG
            Token::U8(128),
            Token::Str("lsu"),
            Token::Seq { len: Some(12) },
            Token::U16(234),
            Token::U16(1),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::U16(0),
            Token::SeqEnd,
            Token::StructEnd,
        ],
    );

    let d = cx
        .parse("1234567890123456789012345678901234567890")
        .unwrap();

    assert_tokens(
        &d,
        &[
            Token::Struct {
                name: "Decimal",
                len: 4,
            },
            Token::Str("digits"),
            Token::U32(36),
            Token::Str("exponent"),
            Token::I32(4),
            Token::Str("bits"),
            Token::U8(0),
            Token::Str("lsu"),
            Token::Seq { len: Some(12) },
            Token::U16(457),
            Token::U16(123),
            Token::U16(890),
            Token::U16(567),
            Token::U16(234),
            Token::U16(901),
            Token::U16(678),
            Token::U16(345),
            Token::U16(012),
            Token::U16(789),
            Token::U16(456),
            Token::U16(123),
            Token::SeqEnd,
            Token::StructEnd,
        ],
    );

    for (json, err) in vec![
        (
            json!(1i32),
            "invalid type: integer `1`, expected struct Decimal",
        ),
        (
            json!(0.5f32),
            "invalid type: floating point `0.5`, expected struct Decimal",
        ),
        (
            json!("-1"),
            "invalid type: string \"-1\", expected struct Decimal",
        ),
    ] {
        assert_eq!(
            serde_json::from_value::<Decimal<N>>(json)
                .unwrap_err()
                .to_string(),
            err
        );
    }

    #[repr(transparent)]
    #[derive(Debug, PartialEq, PartialOrd, Deserialize, Serialize)]
    pub struct PrimitiveDeserializableDecimal<const N: usize>(
        #[serde(with = "dec::serde_decimal_from_non_float_primitives")] pub Decimal<N>,
    );

    for (json, dec) in vec![
        (r#"-1"#, Decimal::try_from(-1i32).unwrap()),
        (r#""6.0E+2""#, Decimal::from_str("6.0E+2").unwrap()),
    ] {
        let deserialized_value: PrimitiveDeserializableDecimal<N> =
            serde_json::from_str(json).expect("deserialization works");
        assert_eq!(deserialized_value.0, dec);
    }

    // Ensure incompatible values do not work.
    for (json, err) in vec![
        (
            r#"true"#,
            "invalid type: boolean `true`, expected struct Decimal or compatible primitive at line 1 column 4",
        ),
        (
            r#"0.5"#,
            "invalid type: floating point `0.5`, expected struct Decimal or compatible primitive at line 1 column 3",
        ),
    ] {
        assert_eq!(
            serde_json::from_str::<PrimitiveDeserializableDecimal<N>>(json)
                .unwrap_err()
                .to_string(),
            err
        );
    }
}

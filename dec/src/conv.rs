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

/// Converts from some arbitrary signed integer `$n` whose size is a multiple of
/// 32 into a decimal of type `$t`.
///
/// `$cx` is a `Context::<$t>` used to generate a value of `$t`. It must outlive
/// the macro call to, e.g., allow checking the context's status.
macro_rules! from_signed_int {
    ($t:ty, $cx:expr, $n:expr) => {
        __from_int!($t, i32, $cx, $n)
    };
}

/// Like `from_signed_int!` but for unsigned integers.
macro_rules! from_unsigned_int {
    ($t:ty, $cx:expr, $n:expr) => {
        __from_int!($t, u32, $cx, $n)
    };
}

macro_rules! __from_int {
    ($t:ty, $l:ty, $cx:expr, $n:expr) => {{
        let n = $n.to_be_bytes();
        assert!(
            n.len() % 4 == 0 && n.len() >= 4,
            "from_int requires size of integer to be a multiple of 32"
        );

        // Process `$n` in 32-bit chunks. Only the first chunk has to be sign
        // aware. Each turn of the loop computes `d = d * 2^32 + n`, where `n`
        // is the next 32-bit chunk.
        let mut d = <$t>::from(<$l>::from_be_bytes(n[..4].try_into().unwrap()));
        for i in (4..n.len()).step_by(4) {
            d = $cx.mul(d, <$t>::TWO_POW_32);
            let n = <$t>::from(u32::from_be_bytes(n[i..i + 4].try_into().unwrap()));
            d = $cx.add(d, n);
        }

        d
    }};
}

macro_rules! decnum_from_signed_int {
    ($t:ty, $cx:expr, $n:expr) => {
        __decnum_from_int!($t, i32, $cx, $n)
    };
}

macro_rules! decnum_from_unsigned_int {
    ($t:ty, $cx:expr, $n:expr) => {
        __decnum_from_int!($t, u32, $cx, $n)
    };
}

// Equivalent to `__from_int`, but with `Decimal`'s API.
macro_rules! __decnum_from_int {
    ($t:ty, $l:ty, $cx:expr, $n:expr) => {{
        let n = $n.to_be_bytes();
        assert!(
            n.len() % 4 == 0 && n.len() >= 4,
            "from_int requires size of integer to be a multiple of 32"
        );
        let two_pow_32 = Decimal::<N>::two_pow_32();

        let mut d = <$t>::from(<$l>::from_be_bytes(n[..4].try_into().unwrap()));
        for i in (4..n.len()).step_by(4) {
            $cx.mul(&mut d, &two_pow_32);
            let n = <$t>::from(u32::from_be_bytes(n[i..i + 4].try_into().unwrap()));
            $cx.add(&mut d, &n);
        }

        d
    }};
}

/// Converts from some decimal into a string in standard notation.
macro_rules! to_standard_notation_string {
    ($d:expr) => {{
        let digits = $d.coefficient_digits();
        let digits = {
            let i = digits.iter().position(|d| *d != 0).unwrap_or(digits.len() - 1);
            &digits[i..]
        };
        let ndigits = digits.len() as i32;
        let e = $d.exponent();
        // We allocate space for all the digits plus a possible "-0." prefix. This is usually an overestimate but is an underestimate for very large or very small scales.
        let mut out = String::with_capacity(digits.len() + 3);
        if $d.is_negative() {
            out.push('-');
        }

        if e >= 0 {
            // All digits before the decimal point.
            for d in digits {
                out.push(char::from(b'0' + *d));
            }
            if !$d.is_zero() {
                for _ in 0..e {
                    out.push('0');
                }
            }
        } else if ndigits > -e {
            // Digits span the decimal point.
            let e = (ndigits + e) as usize;
            for d in &digits[..e] {
                out.push(char::from(b'0' + *d));
            }
            out.push('.');
            for d in &digits[e..] {
                out.push(char::from(b'0' + *d));
            }
        } else {
            // All digits after the decimal point.
            out.push_str("0.");
            for _ in 0..(-e - ndigits) {
                out.push('0');
            }
            for d in digits {
                out.push(char::from(b'0' + *d));
            }
        }
        out
    }};
}

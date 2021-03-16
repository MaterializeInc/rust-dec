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

macro_rules! decimal_from_signed_int {
    ($cx:expr, $n:expr) => {
        __decimal_from_int!(i32, $cx, $n)
    };
}

macro_rules! decimal_from_unsigned_int {
    ($cx:expr, $n:expr) => {
        __decimal_from_int!(u32, $cx, $n)
    };
}

// Equivalent to `__from_int`, but with `Decimal`'s API.
macro_rules! __decimal_from_int {
    ($l:ty, $cx:expr, $n:expr) => {{
        let n = $n.to_be_bytes();
        assert!(
            n.len() % 4 == 0 && n.len() >= 4,
            "from_int requires size of integer to be a multiple of 32"
        );
        let two_pow_32 = Decimal::<N>::two_pow_32();

        let mut d = Decimal::<N>::from(<$l>::from_be_bytes(n[..4].try_into().unwrap()));
        for i in (4..n.len()).step_by(4) {
            $cx.mul(&mut d, &two_pow_32);
            let n = Decimal::<N>::from(u32::from_be_bytes(n[i..i + 4].try_into().unwrap()));
            $cx.add(&mut d, &n);
        }

        d
    }};
}

/// Looks up character representation of a densely packed digit.
macro_rules! dpd2char {
    ($dpd:expr, $digits:expr, $digits_idx:expr) => {{
        let mut u = [0u8; 4];
        let bin_idx = (unsafe { decnumber_sys::DPD2BIN[$dpd] } as usize) << 2;
        u.copy_from_slice(unsafe { &decnumber_sys::BIN2CHAR[bin_idx..bin_idx + 4] });
        if $digits_idx > 0 {
            $digits[$digits_idx..$digits_idx + 3].copy_from_slice(&u[1..4]);
            $digits_idx += 3;
        } else if u[0] > 0 {
            // skip leading zeroes; left align first value
            let d = (4 - u[0]) as usize;
            $digits[$digits_idx..$digits_idx + u[0] as usize].copy_from_slice(&u[d..4]);
            $digits_idx += u[0] as usize;
        }
    }};
}

/// Produces a string-ified version of a `Vec<char>` derived from a decimal.
macro_rules! stringify_digits {
    ($s:expr, $digits:expr, $digits_idx:expr) => {{
        if $digits_idx == 0 {
            $digits[0] = b'0';
            $digits_idx = 1;
        }

        let e = $s.exponent();
        if e >= 0 {
            let mut s = String::with_capacity($digits_idx + e as usize + 1);
            if $s.is_negative() {
                s.push('-');
            }
            s.push_str(unsafe { std::str::from_utf8_unchecked(&$digits[..$digits_idx]) });
            if $digits[0] != b'0' {
                for _ in 0..e {
                    s.push('0');
                }
            }
            s
        } else if $digits_idx as i32 > -e {
            let mut s = String::with_capacity($digits_idx + 2);
            if $s.is_negative() {
                s.push('-');
            }
            let e = ($digits_idx as i32 + e) as usize;
            for d in &$digits[..e] {
                s.push(char::from(*d));
            }
            s.push('.');
            for d in &$digits[e..$digits_idx] {
                s.push(char::from(*d));
            }
            s
        } else {
            let d = usize::try_from(-e).unwrap() - $digits_idx;
            let mut s = String::with_capacity($digits_idx + d + 3);
            if $s.is_negative() {
                s.push('-');
            }
            // All digits after the decimal point.
            s.push_str("0.");
            for _ in 0..d {
                s.push('0');
            }
            for d in &$digits[..$digits_idx] {
                s.push(char::from(*d));
            }
            s
        }
    }};
}

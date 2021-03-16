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

use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use rand::{thread_rng, Rng};

use dec::{Context, Decimal, Decimal128, Decimal64};

fn bench_decode_decimal64(d: Decimal64, b: &mut Bencher) {
    b.iter_with_setup(|| d.clone(), |d| (d.exponent(), d.coefficient()))
}

fn bench_decode_decimal128(d: Decimal128, b: &mut Bencher) {
    b.iter_with_setup(|| d.clone(), |d| (d.exponent(), d.coefficient()))
}

pub fn bench_decode(c: &mut Criterion) {
    // decode_decimal64
    let mut rng = thread_rng();
    let mut cx = Context::<Decimal64>::default();
    let d64 = cx.from_i64(rng.gen());
    c.bench_function("decode_decimal64", |b| bench_decode_decimal64(d64, b));

    // decode_decimal128
    let mut rng = thread_rng();
    let mut cx = Context::<Decimal128>::default();
    let d128 = cx.from_i128(rng.gen());
    c.bench_function("decode_decimal128", |b| bench_decode_decimal128(d128, b));
}

pub fn bench_to_string(d: Decimal128, b: &mut Bencher) {
    b.iter_with_setup(
        || {
            let mut cx = Context::<Decimal128>::default();
            [-50, 0, 50]
                .iter()
                .map(|exp| {
                    let mut d = d.clone();
                    cx.set_exponent(&mut d, *exp);
                    d
                })
                .collect::<Vec<_>>()
        },
        |d| {
            for d in d {
                d.to_string();
            }
        },
    )
}

pub fn bench_to_string_64(d: Decimal64, b: &mut Bencher) {
    b.iter_with_setup(
        || {
            let mut cx = Context::<Decimal64>::default();
            [-50, 0, 50]
                .iter()
                .map(|exp| {
                    let mut d = d.clone();
                    cx.set_exponent(&mut d, *exp);
                    d
                })
                .collect::<Vec<_>>()
        },
        |d| {
            for d in d {
                d.to_string();
            }
        },
    )
}

pub fn bench_standard_notation_string(d: Decimal128, b: &mut Bencher) {
    b.iter_with_setup(
        || {
            let mut cx = Context::<Decimal128>::default();
            [-50, 0, 50]
                .iter()
                .map(|exp| {
                    let mut d = d.clone();
                    cx.set_exponent(&mut d, *exp);
                    d
                })
                .collect::<Vec<_>>()
        },
        |d| {
            for d in d {
                d.to_standard_notation_string();
            }
        },
    )
}

pub fn bench_standard_notation_string_64(d: Decimal64, b: &mut Bencher) {
    b.iter_with_setup(
        || {
            let mut cx = Context::<Decimal64>::default();
            [-50, 0, 50]
                .iter()
                .map(|exp| {
                    let mut d = d.clone();
                    cx.set_exponent(&mut d, *exp);
                    d
                })
                .collect::<Vec<_>>()
        },
        |d| {
            for d in d {
                d.to_standard_notation_string();
            }
        },
    )
}

pub fn bench_print(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut cx = Context::<Decimal128>::default();
    let d128 = cx.from_i128(rng.gen());
    c.bench_function("to_string_dec128", |b| bench_to_string(d128.clone(), b));
    let mut rng = thread_rng();
    let mut cx = Context::<Decimal128>::default();
    let d128 = cx.from_i128(rng.gen());
    c.bench_function("to_standard_notation_string_dec128", |b| {
        bench_standard_notation_string(d128, b)
    });
    let mut rng = thread_rng();
    let mut cx = Context::<Decimal64>::default();
    let d64 = cx.from_i64(rng.gen());
    c.bench_function("to_string_dec64", |b| bench_to_string_64(d64.clone(), b));
    let mut rng = thread_rng();
    let mut cx = Context::<Decimal64>::default();
    let d64 = cx.from_i64(rng.gen());
    c.bench_function("to_standard_notation_string_dec64", |b| {
        bench_standard_notation_string_64(d64, b)
    });
}

pub fn bench_try_into_primitive(d: Decimal<13>, b: &mut Bencher) {
    b.iter_with_setup(
        || {
            [-1, 0, 1]
                .iter()
                .map(|exp| {
                    let mut d = d.clone();
                    d.set_exponent(*exp);
                    d
                })
                .collect::<Vec<_>>()
        },
        |v| {
            for d in v {
                let _ = i128::try_from(d);
            }
        },
    )
}

pub fn bench_tryinto_primitive(c: &mut Criterion) {
    let mut rng = thread_rng();
    let d: Decimal<13> = i32::into(rng.gen());
    c.bench_function("bench_try_into_primitive", |b| {
        bench_try_into_primitive(d.clone(), b)
    });
}

criterion_group!(benches, bench_decode, bench_print, bench_tryinto_primitive);
criterion_main!(benches);

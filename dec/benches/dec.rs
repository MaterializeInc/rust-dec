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

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use itertools::Itertools as _;
use rand::Rng;
use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};

use dec::{Context, Decimal, Decimal128, Decimal64};

use std::{fmt, time::Duration};

const TIME: Duration = Duration::from_secs(15);

fn bench_to_string<T: fmt::Display>(slice: &[T]) {
    for d in slice {
        let string = d.to_string();
        black_box(string);
    }
}

macro_rules! bench_fixed_impl {
    ($bencher: ident, $size: expr, $type: ty, $group: expr) => {
        let mut cx = Context::<$type>::default();
        let mut rng = Xoshiro128StarStar::seed_from_u64(0xdeadbeef);

        let vec: Vec<$type> = (0..$size)
            .into_iter()
            .map(|_| {
                let array = rng.gen();
                <$type>::from_ne_bytes(array)
            })
            .collect();

        let mut group = $bencher.benchmark_group($group);
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("to_string", &vec, |b, vec| b.iter(|| bench_to_string(vec)));
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("to_standard_notation_string", &vec, |b, vec| {
                b.iter(|| {
                    for &d in vec {
                        let string = d.to_standard_notation_string();
                        black_box(string);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("coefficient", &vec, |b, vec| {
                b.iter(|| {
                    for &d in vec {
                        let coeff = d.coefficient();
                        black_box(coeff);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("exponent", &vec, |b, vec| {
                b.iter(|| {
                    for &d in vec {
                        let exp = d.exponent();
                        black_box(exp);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("add", &vec, |b, vec| {
                b.iter(|| {
                    for (&a, &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.add(a, b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("sub", &vec, |b, vec| {
                b.iter(|| {
                    for (&a, &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.sub(a, b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("mul", &vec, |b, vec| {
                b.iter(|| {
                    for (&a, &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.mul(a, b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("div", &vec, |b, vec| {
                b.iter(|| {
                    for (&a, &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.div(a, b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("abs", &vec, |b, vec| {
                b.iter(|| {
                    for &d in vec {
                        let v = cx.abs(d);
                        black_box(v);
                    }
                })
            });
        group.finish();
    };
}

fn bench_fixed_size(bencher: &mut Criterion) {
    const SIZE: u64 = 10_000;

    bench_fixed_impl!(bencher, SIZE, Decimal64, "Decimal64");
    bench_fixed_impl!(bencher, SIZE, Decimal128, "Decimal128");
}

macro_rules! bench_dyn_impl {
    ($bencher: ident, $size: expr, $type: ty, $group: expr) => {
        let mut cx = Context::<$type>::default();
        let mut rng = Xoshiro128StarStar::seed_from_u64(0xdeadbeef);

        let vec: Vec<$type> = (0..$size)
            .into_iter()
            .map(|_| {
                let array = rng.gen();
                Decimal128::from_ne_bytes(array).into()
            })
            .collect();

        let mut group = $bencher.benchmark_group($group);
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("to_string", &vec, |b, vec| b.iter(|| bench_to_string(vec)));
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("to_standard_notation_string", &vec, |b, vec| {
                b.iter(|| {
                    for &d in vec {
                        let string = d.to_standard_notation_string();
                        black_box(string);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("coefficient", &vec, |b, vec| {
                b.iter(|| {
                    for &(mut d) in vec {
                        let res = d.coefficient::<$type>();
                        let _ = black_box(res);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("exponent", &vec, |b, vec| {
                b.iter(|| {
                    for &d in vec {
                        let exp = d.exponent();
                        black_box(exp);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("add", &vec, |b, vec| {
                b.iter(|| {
                    for (&(mut a), &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.add(&mut a, &b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("sub", &vec, |b, vec| {
                b.iter(|| {
                    for (&(mut a), &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.sub(&mut a, &b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("mul", &vec, |b, vec| {
                b.iter(|| {
                    for (&(mut a), &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.mul(&mut a, &b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE / 2))
            .bench_with_input("div", &vec, |b, vec| {
                b.iter(|| {
                    for (&(mut a), &b) in vec.iter().tuples::<(_, _)>() {
                        let c = cx.div(&mut a, &b);
                        black_box(c);
                    }
                })
            });
        group
            .measurement_time(TIME)
            .throughput(Throughput::Elements(SIZE))
            .bench_with_input("abs", &vec, |b, vec| {
                b.iter(|| {
                    for &(mut d) in vec {
                        let v = cx.abs(&mut d);
                        black_box(v);
                    }
                })
            });
        group.finish();
    };
}

fn bench_dyn_size(bencher: &mut Criterion) {
    const SIZE: u64 = 10_000;

    bench_dyn_impl!(bencher, SIZE, Decimal<12>, "Decimal<12>");
    bench_dyn_impl!(bencher, SIZE, Decimal<16>, "Decimal<16>");
}

criterion_group!(benches, bench_fixed_size, bench_dyn_size);
criterion_main!(benches);

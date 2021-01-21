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
use std::convert::TryInto;
use std::error::Error;
use std::fmt;

use dec::{Decimal128, Decimal32, Decimal64};

use crate::ast;
use crate::backend::{Backend, BackendError, BackendResult};

pub enum Outcome {
    Passed,
    Failed { cause: Box<dyn Error> },
    Skipped,
}

pub trait Report {
    fn start_file(&mut self, file: &ast::File);
    fn finish_file(&mut self);
    fn start_test(&mut self, test: &ast::Test);
    fn finish_test(&mut self, outcome: Outcome);
}

pub fn run_file<B, R>(reporter: &mut R, file: &ast::File) -> Result<(), Box<dyn Error>>
where
    B: Backend,
    R: Report,
{
    reporter.start_file(file);
    let mut backend = B::new();
    for line in &file.lines {
        match line {
            ast::Line::Directive(directive) => run_directive(&mut backend, reporter, directive)?,
            ast::Line::Test(test) => run_test(&mut backend, reporter, test),
        }
    }
    reporter.finish_file();
    Ok(())
}

fn run_directive<B, R>(
    backend: &mut B,
    reporter: &mut R,
    directive: &ast::Directive,
) -> Result<(), Box<dyn Error>>
where
    B: Backend,
    R: Report,
{
    let res = match directive {
        ast::Directive::Clamp(clamp) => backend.set_clamp(*clamp),
        ast::Directive::Extended(extended) => backend.set_extended(*extended),
        ast::Directive::MaxExponent(e) => backend.set_max_exponent(*e),
        ast::Directive::MinExponent(e) => backend.set_min_exponent(*e),
        ast::Directive::Precision(p) => backend.set_precision(*p),
        ast::Directive::Rounding(rounding) => backend.set_rounding(*rounding),
        ast::Directive::DecTest(file) => {
            run_file::<B, _>(reporter, file)?;
            Ok(())
        }
        ast::Directive::Version(_) => Ok(()),
    };
    res.map_err(|e| match e {
        BackendError::Failure { cause } => cause,
        BackendError::Unsupported => {
            format!("backend does not support directive \"{}\"", directive).into()
        }
    })
}

fn run_test<B, R>(backend: &mut B, reporter: &mut R, test: &ast::Test)
where
    B: Backend,
    R: Report,
{
    reporter.start_test(&test);
    let outcome = match run_test_inner(backend, test) {
        Ok(()) => Outcome::Passed,
        Err(BackendError::Failure { cause }) => Outcome::Failed { cause },
        Err(BackendError::Unsupported) => Outcome::Skipped,
    };
    reporter.finish_test(outcome);
}

fn run_test_inner<B>(backend: &mut B, test: &ast::Test) -> BackendResult<()>
where
    B: Backend,
{
    backend.clear_status();

    if !backend.is_valid(&test.id) {
        return Err(BackendError::Unsupported);
    }

    match &test.operation {
        ast::Operation::Abs(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.abs(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Add(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.add(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::And(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.and(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Apply(n) => {
            let n = parse_operand_imprecise(backend, n)?;
            check_result(backend, &test.result, &n)?;
        }
        ast::Operation::Canonical(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.canonical(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Class(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.class(n)?.to_string();
            check_result_str(&test.result, &result)?;
        }
        ast::Operation::Compare(lhs, rhs) => {
            // Comparison in dec returns Rust's `std::cmp::Ordering` enumeration
            // so we lose the actual number returned from libdecnumber. So skip
            // any assertions about the exact encoding of the returned number,
            // and strip off any sign/payload from NaNs.
            if test.result.starts_with("#") {
                return Err(BackendError::Unsupported);
            }
            let test_result = if test.result.contains("NaN") {
                "NaN"
            } else {
                &test.result
            };
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = match backend.partial_cmp(lhs, rhs)? {
                None => B::nan(),
                Some(Ordering::Less) => parse_operand(backend, "-1")?,
                Some(Ordering::Equal) => parse_operand(backend, "0")?,
                Some(Ordering::Greater) => parse_operand(backend, "1")?,
            };
            check_result(backend, test_result, &result)?;
        }
        ast::Operation::CompareSig(_, _) => return Err(BackendError::Unsupported),
        ast::Operation::CompareTotal(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = match backend.total_cmp(lhs, rhs)? {
                Ordering::Less => parse_operand(backend, "-1")?,
                Ordering::Equal => parse_operand(backend, "0")?,
                Ordering::Greater => parse_operand(backend, "1")?,
            };
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::CompareTotalMag(_, _) => return Err(BackendError::Unsupported),
        ast::Operation::Copy(_) => return Err(BackendError::Unsupported),
        ast::Operation::CopyAbs(_) => return Err(BackendError::Unsupported),
        ast::Operation::CopyNegate(_) => return Err(BackendError::Unsupported),
        ast::Operation::CopySign(_, _) => return Err(BackendError::Unsupported),
        ast::Operation::Divide(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.div(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::DivideInt(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.div_integer(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Exp(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.exp(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Fma(x, y, z) => {
            let x = parse_operand(backend, x)?;
            let y = parse_operand(backend, y)?;
            let z = parse_operand(backend, z)?;
            let result = backend.fma(x, y, z)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Multiply(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.mul(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Invert(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.invert(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Ln(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.ln(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Log10(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.log10(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Logb(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.logb(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Max(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.max(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::MaxMag(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.max_abs(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Min(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.min(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::MinMag(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.min_abs(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Minus(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.minus(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::NextMinus(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.next_minus(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::NextPlus(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.next_plus(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::NextToward(x, y) => {
            let x = parse_operand(backend, x)?;
            let y = parse_operand(backend, y)?;
            let result = backend.next_toward(x, y)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Or(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.or(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Plus(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.plus(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Power(x, y) => {
            let x = parse_operand(backend, x)?;
            let y = parse_operand(backend, y)?;
            let result = backend.pow(x, y)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Quantize(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.quantize(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Reduce(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.reduce(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Remainder(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.rem(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::RemainderNear(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.rem_near(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Rescale(_, _) => return Err(BackendError::Unsupported),
        ast::Operation::Rotate(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.rotate(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::SameQuantum(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = match backend.quantum_matches(lhs, rhs)? {
                false => "0",
                true => "1",
            };
            check_result_str(&test.result, &result)?;
        }
        ast::Operation::Scaleb(x, y) => {
            let x = parse_operand(backend, x)?;
            let y = parse_operand(backend, y)?;
            let result = backend.scaleb(x, y)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Shift(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.shift(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::SquareRoot(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.sqrt(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::Subtract(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.sub(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::ToEng(n) => {
            let n = parse_operand_imprecise(backend, n)?;
            let result = format!("{:#}", n);
            check_result_str(&test.result, &result)?;
        }
        ast::Operation::ToIntegral(_) => return Err(BackendError::Unsupported),
        ast::Operation::ToIntegralX(n) => {
            let n = parse_operand(backend, n)?;
            let result = backend.round(n)?;
            check_result(backend, &test.result, &result)?;
        }
        ast::Operation::ToSci(n) => {
            let n = parse_operand_imprecise(backend, n)?;
            let result = n.to_string();
            check_result_str(&test.result, &result)?;
        }
        ast::Operation::Trim(_) => return Err(BackendError::Unsupported),
        ast::Operation::Xor(lhs, rhs) => {
            let lhs = parse_operand(backend, lhs)?;
            let rhs = parse_operand(backend, rhs)?;
            let result = backend.xor(lhs, rhs)?;
            check_result(backend, &test.result, &result)?;
        }
    }

    // TODO(benesch): check status flags.

    Ok(())
}

fn parse_operand<B>(backend: &mut B, operand: &str) -> BackendResult<B::D>
where
    B: Backend,
{
    let op = parse_operand_inner(backend, operand, true)?;
    if backend.status().inexact() {
        // The backend was incapable of representing the operand exactly, so
        // we have to skip the test case.
        Err(BackendError::Unsupported)
    } else {
        Ok(op)
    }
}

fn parse_operand_imprecise<B>(backend: &mut B, operand: &str) -> BackendResult<B::D>
where
    B: Backend,
{
    parse_operand_inner(backend, operand, false)
}

fn parse_operand_inner<B>(backend: &mut B, operand: &str, precise: bool) -> BackendResult<B::D>
where
    B: Backend,
{
    if operand == "#" {
        Err(BackendError::Unsupported)
    } else if let Some(bytes) = operand.strip_prefix("#") {
        let bytes = hex::decode(bytes)?;
        match bytes.len() {
            4 => {
                let bytes = bytes.try_into().unwrap();
                Ok(backend.from_decimal32(Decimal32::from_be_bytes(bytes)))
            }
            8 => {
                let bytes = bytes.try_into().unwrap();
                Ok(backend.from_decimal64(Decimal64::from_be_bytes(bytes)))
            }
            16 => {
                let bytes = bytes.try_into().unwrap();
                Ok(backend.from_decimal128(Decimal128::from_be_bytes(bytes)))
            }
            _ => Err(BackendError::failure(format!(
                "incorrect byte literal with {} bytes",
                bytes.len()
            ))),
        }
    } else if let Some(s) = operand.strip_prefix("32#") {
        Ok(backend.from_decimal32(s.parse()?))
    } else if let Some(s) = operand.strip_prefix("64#") {
        Ok(backend.from_decimal64(s.parse()?))
    } else if let Some(s) = operand.strip_prefix("128#") {
        Ok(backend.from_decimal128(s.parse()?))
    } else {
        Ok(backend.parse(operand, precise))
    }
}

fn check_result<B>(backend: &mut B, expected: &str, actual: &B::D) -> BackendResult<()>
where
    B: Backend,
{
    enum Expected<B>
    where
        B: Backend,
    {
        Decimal32(Decimal32),
        Decimal64(Decimal64),
        Decimal128(Decimal128),
        Backend(B::D),
    }

    impl<B> fmt::Display for Expected<B>
    where
        B: Backend,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Expected::Decimal32(d) => write!(f, "{}", d),
                Expected::Decimal64(d) => write!(f, "{}", d),
                Expected::Decimal128(d) => write!(f, "{}", d),
                Expected::Backend(d) => write!(f, "{}", d),
            }
        }
    }

    let expected: Expected<B> = if let Some(bytes) = expected.strip_prefix("#") {
        let bytes = hex::decode(bytes)?;
        match bytes.len() {
            4 => {
                let bytes = bytes.try_into().unwrap();
                Expected::Decimal32(Decimal32::from_be_bytes(bytes))
            }
            8 => {
                let bytes = bytes.try_into().unwrap();
                Expected::Decimal64(Decimal64::from_be_bytes(bytes))
            }
            16 => {
                let bytes = bytes.try_into().unwrap();
                Expected::Decimal128(Decimal128::from_be_bytes(bytes))
            }
            _ => {
                return Err(BackendError::failure(format!(
                    "incorrect byte literal with {} bytes",
                    bytes.len()
                )))
            }
        }
    } else if let Some(s) = expected.strip_prefix("32#") {
        Expected::Decimal32(s.parse()?)
    } else if let Some(s) = expected.strip_prefix("64#") {
        Expected::Decimal64(s.parse()?)
    } else if let Some(s) = expected.strip_prefix("128#") {
        Expected::Decimal128(s.parse()?)
    } else {
        let mut backend = B::new();
        let result = backend.parse(expected, true);
        if backend.status().inexact() {
            // The backend was incapable of representing the operand exactly, so
            // we have to skip the test case.
            return Err(BackendError::Unsupported);
        }
        Expected::Backend(result)
    };

    let actual = match &expected {
        Expected::Decimal32(_) => backend.to_decimal32(actual).to_string(),
        Expected::Decimal64(_) => backend.to_decimal64(actual).to_string(),
        Expected::Decimal128(_) => backend.to_decimal128(actual).to_string(),
        Expected::Backend(_) => actual.to_string(),
    };

    check_result_str(&expected.to_string(), &actual)
}

fn check_result_str(expected: &str, actual: &str) -> Result<(), BackendError> {
    if expected == actual {
        Ok(())
    } else {
        Err(BackendError::failure(format!(
            "got {} but expected {}",
            actual, expected
        )))
    }
}

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

use std::fmt;
use std::path::PathBuf;

#[derive(Debug)]
pub struct File {
    pub path: PathBuf,
    pub lines: Vec<Line>,
}

#[derive(Debug)]
pub enum Line {
    Directive(Directive),
    Test(Test),
}

#[derive(Debug)]
pub enum Directive {
    Clamp(bool),
    DecTest(File),
    Extended(bool),
    MaxExponent(isize),
    MinExponent(isize),
    Precision(usize),
    Rounding(dec::Rounding),
    Version(String),
}

impl fmt::Display for Directive {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Directive::Clamp(clamp) => write!(f, "clamp: {}", clamp),
            Directive::DecTest(file) => write!(f, "dectest: {}", file.path.display()),
            Directive::Extended(extended) => write!(f, "extended: {}", extended),
            Directive::MaxExponent(e) => write!(f, "maxExponent: {}", e),
            Directive::MinExponent(e) => write!(f, "minExponent: {}", e),
            Directive::Precision(p) => write!(f, "precision: {}", p),
            Directive::Rounding(r) => {
                f.write_str("rounding: ")?;
                match r {
                    dec::Rounding::Ceiling => f.write_str("ceiling"),
                    dec::Rounding::Down => f.write_str("down"),
                    dec::Rounding::Floor => f.write_str("floor"),
                    dec::Rounding::HalfDown => f.write_str("half_down"),
                    dec::Rounding::HalfEven => f.write_str("half_even"),
                    dec::Rounding::HalfUp => f.write_str("half_up"),
                    dec::Rounding::Up => f.write_str("up"),
                    dec::Rounding::ZeroFiveUp => f.write_str("zero_five"),
                }
            }
            Directive::Version(v) => write!(f, "version: {}", v),
        }
    }
}

#[derive(Debug)]
pub struct Test {
    pub id: String,
    pub operation: Operation,
    pub result: String,
    pub conditions: Vec<Condition>,
}

#[derive(Debug)]
pub enum Operation {
    Abs(String),
    Add(String, String),
    And(String, String),
    Apply(String),
    Canonical(String),
    Class(String),
    Compare(String, String),
    CompareSig(String, String),
    CompareTotal(String, String),
    CompareTotalMag(String, String),
    Copy(String),
    CopyAbs(String),
    CopyNegate(String),
    CopySign(String, String),
    Divide(String, String),
    DivideInt(String, String),
    Exp(String),
    Fma(String, String, String),
    Invert(String),
    Ln(String),
    Log10(String),
    Logb(String),
    Max(String, String),
    Min(String, String),
    MaxMag(String, String),
    MinMag(String, String),
    Minus(String),
    Multiply(String, String),
    NextMinus(String),
    NextPlus(String),
    NextToward(String, String),
    Or(String, String),
    Plus(String),
    Power(String, String),
    Quantize(String, String),
    Reduce(String),
    Remainder(String, String),
    RemainderNear(String, String),
    Rescale(String, String),
    Rotate(String, String),
    SameQuantum(String, String),
    Scaleb(String, String),
    Shift(String, String),
    SquareRoot(String),
    Subtract(String, String),
    ToEng(String),
    ToIntegral(String),
    ToIntegralX(String),
    ToSci(String),
    Trim(String),
    Xor(String, String),
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operation::Abs(op) => write!(f, "abs {}", op),
            Operation::Add(op1, op2) => write!(f, "add {} {}", op1, op2),
            Operation::And(op1, op2) => write!(f, "and {} {}", op1, op2),
            Operation::Apply(op) => write!(f, "apply {}", op),
            Operation::Canonical(op) => write!(f, "canonical {}", op),
            Operation::Class(op) => write!(f, "class {}", op),
            Operation::Compare(op1, op2) => write!(f, "compare {} {}", op1, op2),
            Operation::CompareSig(op1, op2) => write!(f, "comparesig {} {}", op1, op2),
            Operation::CompareTotal(op1, op2) => write!(f, "comparetotal {} {}", op1, op2),
            Operation::CompareTotalMag(op1, op2) => write!(f, "comparetotalmag {} {}", op1, op2),
            Operation::Copy(op) => write!(f, "copy {}", op),
            Operation::CopyAbs(op) => write!(f, "copyabs {}", op),
            Operation::CopyNegate(op) => write!(f, "copynegate {}", op),
            Operation::CopySign(op1, op2) => write!(f, "copysign {} {}", op1, op2),
            Operation::Divide(op1, op2) => write!(f, "divide {} {}", op1, op2),
            Operation::DivideInt(op1, op2) => write!(f, "divideint {} {}", op1, op2),
            Operation::Exp(op) => write!(f, "exp {}", op),
            Operation::Fma(op1, op2, op3) => write!(f, "fma {} {} {}", op1, op2, op3),
            Operation::Invert(op) => write!(f, "invert {}", op),
            Operation::Ln(op) => write!(f, "ln {}", op),
            Operation::Log10(op) => write!(f, "log10 {}", op),
            Operation::Logb(op) => write!(f, "logb {}", op),
            Operation::Max(op1, op2) => write!(f, "max {} {}", op1, op2),
            Operation::Min(op1, op2) => write!(f, "min {} {}", op1, op2),
            Operation::MaxMag(op1, op2) => write!(f, "maxmag {} {}", op1, op2),
            Operation::MinMag(op1, op2) => write!(f, "minmag {} {}", op1, op2),
            Operation::Minus(op) => write!(f, "minus {}", op),
            Operation::Multiply(op1, op2) => write!(f, "multiply {} {}", op1, op2),
            Operation::NextMinus(op) => write!(f, "nextminus {}", op),
            Operation::NextPlus(op) => write!(f, "nextplus {}", op),
            Operation::NextToward(op1, op2) => write!(f, "nexttoward {} {}", op1, op2),
            Operation::Or(op1, op2) => write!(f, "or {} {}", op1, op2),
            Operation::Plus(op) => write!(f, "plus {}", op),
            Operation::Power(op1, op2) => write!(f, "power {} {}", op1, op2),
            Operation::Quantize(op1, op2) => write!(f, "quantize {} {}", op1, op2),
            Operation::Reduce(op) => write!(f, "reduce {}", op),
            Operation::Remainder(op1, op2) => write!(f, "remainder {} {}", op1, op2),
            Operation::RemainderNear(op1, op2) => write!(f, "remaindernear {} {}", op1, op2),
            Operation::Rescale(op1, op2) => write!(f, "rescale {} {}", op1, op2),
            Operation::Rotate(op1, op2) => write!(f, "rotate {} {}", op1, op2),
            Operation::SameQuantum(op1, op2) => write!(f, "samequantum {} {}", op1, op2),
            Operation::Scaleb(op1, op2) => write!(f, "scaleb {} {}", op1, op2),
            Operation::Shift(op1, op2) => write!(f, "shift {} {}", op1, op2),
            Operation::SquareRoot(op) => write!(f, "squareroot {}", op),
            Operation::Subtract(op1, op2) => write!(f, "subtract {} {}", op1, op2),
            Operation::ToEng(op) => write!(f, "toeng {}", op),
            Operation::ToIntegral(op) => write!(f, "tointegral {}", op),
            Operation::ToIntegralX(op) => write!(f, "tointegralx {}", op),
            Operation::ToSci(op) => write!(f, "tosci {}", op),
            Operation::Trim(op) => write!(f, "trim {}", op),
            Operation::Xor(op1, op2) => write!(f, "xor {} {}", op1, op2),
        }
    }
}

#[derive(Debug)]
pub enum Condition {
    Clamped,
    ConversionSyntax,
    DivisionByZero,
    DivisionImpossible,
    DivisionUndefined,
    Inexact,
    InsufficientStorage,
    InvalidContext,
    InvalidOperation,
    LostDigits,
    Overflow,
    Rounded,
    Subnormal,
    Underflow,
}

impl fmt::Display for Condition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Condition::Clamped => f.write_str("Clamped"),
            Condition::ConversionSyntax => f.write_str("ConversionSyntax"),
            Condition::DivisionByZero => f.write_str("DivisionByZero"),
            Condition::DivisionImpossible => f.write_str("DivisionImpossible"),
            Condition::DivisionUndefined => f.write_str("DivisionUndefined"),
            Condition::Inexact => f.write_str("Inexact"),
            Condition::InsufficientStorage => f.write_str("InsufficientStorage"),
            Condition::InvalidContext => f.write_str("InvalidContext"),
            Condition::InvalidOperation => f.write_str("InvalidOperation"),
            Condition::LostDigits => f.write_str("LostDigits"),
            Condition::Overflow => f.write_str("Overflow"),
            Condition::Rounded => f.write_str("Rounded"),
            Condition::Subnormal => f.write_str("Subnormal"),
            Condition::Underflow => f.write_str("Underflow"),
        }
    }
}

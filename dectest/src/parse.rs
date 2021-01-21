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

use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::str::FromStr;

use crate::ast;
use crate::lex::LexBuf;

struct Context<'a> {
    path: &'a Path,
}

pub fn parse_file(path: &Path) -> Result<ast::File, Box<dyn Error>> {
    let cx = &Context { path };
    let f = BufReader::new(File::open(path)?);
    let mut lines = vec![];
    for (i, line) in f.lines().enumerate() {
        let line = line?;
        let mut buf = LexBuf::new(&line);
        match parse_line(cx, &mut buf) {
            Ok(None) => (),
            Ok(Some(line)) => lines.push(line),
            Err(e) => return Err(format!("parsing line {}: {}", i + 1, e).into()),
        }
    }
    Ok(ast::File {
        path: path.to_path_buf(),
        lines,
    })
}

fn parse_line(cx: &Context, buf: &mut LexBuf) -> Result<Option<ast::Line>, Box<dyn Error>> {
    let token = match parse_token(buf) {
        None => return Ok(None),
        Some(token) => token,
    };
    if let Some(keyword) = token.strip_suffix(":") {
        let value = require_token(buf, "value")?;
        Ok(Some(ast::Line::Directive(parse_directive(
            cx, keyword, value,
        )?)))
    } else {
        let id = token;
        let operation = parse_operation(buf)?;
        if require_token(buf, "->")? != "->" {
            return Err(format!("missing \"->\" token").into());
        }
        let result = require_token(buf, "result")?;
        let mut conditions = vec![];
        while let Some(condition) = parse_token(buf) {
            conditions.push(condition.parse()?);
        }
        Ok(Some(ast::Line::Test(ast::Test {
            id,
            operation,
            result,
            conditions,
        })))
    }
}

fn require_token(buf: &mut LexBuf, name: &str) -> Result<String, Box<dyn Error>> {
    parse_token(buf).ok_or_else(|| format!("missing \"{}\" token", name).into())
}

fn parse_token(buf: &mut LexBuf) -> Option<String> {
    while buf.consume(" ") {}

    if buf.consume("--") {
        while let Some(_) = buf.next() {}
        return None;
    }

    match buf.peek() {
        Some(quote @ '\'') | Some(quote @ '"') => {
            buf.next();
            parse_quoted_token(buf, quote)
        }
        _ => parse_unquoted_token(buf),
    }
}

fn parse_unquoted_token(buf: &mut LexBuf) -> Option<String> {
    let mut token = String::new();
    while let Some(ch) = buf.peek() {
        match ch {
            ' ' => break,
            ch => {
                token.push(ch);
                buf.next();
            }
        }
    }
    if token.is_empty() {
        None
    } else {
        Some(token)
    }
}

fn parse_quoted_token(buf: &mut LexBuf, quote: char) -> Option<String> {
    let mut token = String::new();
    while let Some(ch) = buf.next() {
        if ch == quote {
            if buf.peek() == Some(quote) {
                token.push(quote);
                buf.next();
            } else {
                break;
            }
        } else {
            token.push(ch);
        }
    }
    Some(token)
}

fn parse_directive(
    cx: &Context,
    keyword: &str,
    value: String,
) -> Result<ast::Directive, Box<dyn Error>> {
    match keyword.to_lowercase().as_str() {
        "clamp" => Ok(ast::Directive::Clamp(parse_bool(&value)?)),
        "dectest" => {
            let path = cx.path.with_file_name(value).with_extension("decTest");
            let file =
                parse_file(&path).map_err(|e| format!("opening {}: {}", path.display(), e))?;
            Ok(ast::Directive::DecTest(file))
        }
        "extended" => Ok(ast::Directive::Extended(parse_bool(&value)?)),
        "maxexponent" => Ok(ast::Directive::MaxExponent(value.parse()?)),
        "minexponent" => Ok(ast::Directive::MinExponent(value.parse()?)),
        "rounding" => Ok(ast::Directive::Rounding(parse_rounding(&value)?)),
        "precision" => Ok(ast::Directive::Precision(value.parse()?)),
        "version" => Ok(ast::Directive::Version(value)),
        _ => Err(format!("unknown directive \"{}\"", keyword).into()),
    }
}

fn parse_rounding(s: &str) -> Result<dec::Rounding, Box<dyn Error>> {
    match s {
        "ceiling" => Ok(dec::Rounding::Ceiling),
        "down" => Ok(dec::Rounding::Down),
        "floor" => Ok(dec::Rounding::Floor),
        "half_down" => Ok(dec::Rounding::HalfDown),
        "half_even" => Ok(dec::Rounding::HalfEven),
        "half_up" => Ok(dec::Rounding::HalfUp),
        "up" => Ok(dec::Rounding::Up),
        "05up" => Ok(dec::Rounding::ZeroFiveUp),
        _ => Err(format!("unknown rounding mode \"{}\"", s).into()),
    }
}

fn parse_bool(s: &str) -> Result<bool, Box<dyn Error>> {
    match s {
        "0" => Ok(false),
        "1" => Ok(true),
        _ => Err(format!("invalid boolean \"{}\"", s).into()),
    }
}

fn parse_operation(buf: &mut LexBuf) -> Result<ast::Operation, Box<dyn Error>> {
    let operation = require_token(buf, "operation")?;
    let mut op = || require_token(buf, "operand");
    match operation.to_lowercase().as_str() {
        "abs" => Ok(ast::Operation::Abs(op()?)),
        "add" => Ok(ast::Operation::Add(op()?, op()?)),
        "and" => Ok(ast::Operation::And(op()?, op()?)),
        "apply" => Ok(ast::Operation::Apply(op()?)),
        "canonical" => Ok(ast::Operation::Canonical(op()?)),
        "class" => Ok(ast::Operation::Class(op()?)),
        "compare" => Ok(ast::Operation::Compare(op()?, op()?)),
        "comparesig" => Ok(ast::Operation::CompareSig(op()?, op()?)),
        "comparetotal" => Ok(ast::Operation::CompareTotal(op()?, op()?)),
        "comparetotmag" => Ok(ast::Operation::CompareTotalMag(op()?, op()?)),
        "copy" => Ok(ast::Operation::Copy(op()?)),
        "copyabs" => Ok(ast::Operation::CopyAbs(op()?)),
        "copynegate" => Ok(ast::Operation::CopyNegate(op()?)),
        "copysign" => Ok(ast::Operation::CopySign(op()?, op()?)),
        "divide" => Ok(ast::Operation::Divide(op()?, op()?)),
        "divideint" => Ok(ast::Operation::DivideInt(op()?, op()?)),
        "exp" => Ok(ast::Operation::Exp(op()?)),
        "fma" => Ok(ast::Operation::Fma(op()?, op()?, op()?)),
        "invert" => Ok(ast::Operation::Invert(op()?)),
        "ln" => Ok(ast::Operation::Ln(op()?)),
        "log10" => Ok(ast::Operation::Log10(op()?)),
        "logb" => Ok(ast::Operation::Logb(op()?)),
        "max" => Ok(ast::Operation::Max(op()?, op()?)),
        "min" => Ok(ast::Operation::Min(op()?, op()?)),
        "maxmag" => Ok(ast::Operation::MaxMag(op()?, op()?)),
        "minmag" => Ok(ast::Operation::MinMag(op()?, op()?)),
        "minus" => Ok(ast::Operation::Minus(op()?)),
        "multiply" => Ok(ast::Operation::Multiply(op()?, op()?)),
        "nextminus" => Ok(ast::Operation::NextMinus(op()?)),
        "nextplus" => Ok(ast::Operation::NextPlus(op()?)),
        "nexttoward" => Ok(ast::Operation::NextToward(op()?, op()?)),
        "or" => Ok(ast::Operation::Or(op()?, op()?)),
        "plus" => Ok(ast::Operation::Plus(op()?)),
        "power" => Ok(ast::Operation::Power(op()?, op()?)),
        "quantize" => Ok(ast::Operation::Quantize(op()?, op()?)),
        "reduce" => Ok(ast::Operation::Reduce(op()?)),
        "remainder" => Ok(ast::Operation::Remainder(op()?, op()?)),
        "remaindernear" => Ok(ast::Operation::RemainderNear(op()?, op()?)),
        "rescale" => Ok(ast::Operation::Rescale(op()?, op()?)),
        "rotate" => Ok(ast::Operation::Rotate(op()?, op()?)),
        "samequantum" => Ok(ast::Operation::SameQuantum(op()?, op()?)),
        "scaleb" => Ok(ast::Operation::Scaleb(op()?, op()?)),
        "shift" => Ok(ast::Operation::Shift(op()?, op()?)),
        "squareroot" => Ok(ast::Operation::SquareRoot(op()?)),
        "subtract" => Ok(ast::Operation::Subtract(op()?, op()?)),
        "toeng" => Ok(ast::Operation::ToEng(op()?)),
        "tointegral" => Ok(ast::Operation::ToIntegral(op()?)),
        "tointegralx" => Ok(ast::Operation::ToIntegralX(op()?)),
        "tosci" => Ok(ast::Operation::ToSci(op()?)),
        "trim" => Ok(ast::Operation::Trim(op()?)),
        "xor" => Ok(ast::Operation::Xor(op()?, op()?)),
        _ => Err(format!("unknown operation \"{}\"", operation).into()),
    }
}

impl FromStr for ast::Condition {
    type Err = Box<dyn Error>;

    fn from_str(s: &str) -> Result<ast::Condition, Box<dyn Error>> {
        match s.to_lowercase().as_str() {
            "clamped" => Ok(ast::Condition::Clamped),
            "conversion_syntax" => Ok(ast::Condition::ConversionSyntax),
            "division_by_zero" => Ok(ast::Condition::DivisionByZero),
            "division_impossible" => Ok(ast::Condition::DivisionImpossible),
            "division_undefined" => Ok(ast::Condition::DivisionUndefined),
            "inexact" => Ok(ast::Condition::Inexact),
            "insufficient_storage" => Ok(ast::Condition::InsufficientStorage),
            "invalid_context" => Ok(ast::Condition::InvalidContext),
            "invalid_operation" => Ok(ast::Condition::InvalidOperation),
            "lost_digits" => Ok(ast::Condition::LostDigits),
            "overflow" => Ok(ast::Condition::Overflow),
            "rounded" => Ok(ast::Condition::Rounded),
            "subnormal" => Ok(ast::Condition::Subnormal),
            "underflow" => Ok(ast::Condition::Underflow),
            _ => Err(format!("unknown condition \"{}\"", s).into()),
        }
    }
}

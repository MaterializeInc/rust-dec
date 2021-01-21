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
use std::fmt;

/// An error indicating that a string is not a valid decimal number.
#[derive(Debug, Eq, PartialEq)]
pub struct ParseDecimalError;

impl fmt::Display for ParseDecimalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid decimal syntax")
    }
}

impl Error for ParseDecimalError {}

/// An error indicating that a precision is not valid for a given context.
#[derive(Debug, Eq, PartialEq)]
pub struct InvalidPrecisionError;

impl fmt::Display for InvalidPrecisionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid decimal precision")
    }
}

impl Error for InvalidPrecisionError {}

/// An error indicating that a minimum exponent or maximum exponent is not valid
/// for a given context.
#[derive(Debug, Eq, PartialEq)]
pub struct InvalidExponentError;

impl fmt::Display for InvalidExponentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid decimal exponent")
    }
}

impl Error for InvalidExponentError {}

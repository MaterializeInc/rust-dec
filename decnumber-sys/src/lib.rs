// Copyright Materialize, Inc. All rights reserved.
//
// This software is made available under the terms of the
// ICU license -- ICU 1.8.1 and later.

#![allow(non_camel_case_types, non_upper_case_globals, non_snake_case)]

//! Bindings to libdecnumber.
//!
//! This crate provides raw bindings to [libdecnumber], an implementation of the
//! [General Decimal Arithmetic][gda] specification.
//!
//! This crate bundles the latest release of libdecnumber, v3.68.
//!
//! [gda]: http://speleotrove.com/decimal/
//! [libdecnumber]: http://speleotrove.com/decimal/

use libc::{c_char, c_uint};

pub type rounding = c_uint;
pub const DEC_ROUND_CEILING: rounding = 0;
pub const DEC_ROUND_UP: rounding = 1;
pub const DEC_ROUND_HALF_UP: rounding = 2;
pub const DEC_ROUND_HALF_EVEN: rounding = 3;
pub const DEC_ROUND_HALF_DOWN: rounding = 4;
pub const DEC_ROUND_DOWN: rounding = 5;
pub const DEC_ROUND_FLOOR: rounding = 6;
pub const DEC_ROUND_05UP: rounding = 7;
pub const DEC_ROUND_MAX: rounding = 8;

pub type decClass = c_uint;
pub const DEC_CLASS_SNAN: decClass = 0;
pub const DEC_CLASS_QNAN: decClass = 1;
pub const DEC_CLASS_NEG_INF: decClass = 2;
pub const DEC_CLASS_NEG_NORMAL: decClass = 3;
pub const DEC_CLASS_NEG_SUBNORMAL: decClass = 4;
pub const DEC_CLASS_NEG_ZERO: decClass = 5;
pub const DEC_CLASS_POS_ZERO: decClass = 6;
pub const DEC_CLASS_POS_SUBNORMAL: decClass = 7;
pub const DEC_CLASS_POS_NORMAL: decClass = 8;
pub const DEC_CLASS_POS_INF: decClass = 9;

pub const DEC_INIT_BASE: i32 = 0;
pub const DEC_INIT_DECIMAL32: i32 = 32;
pub const DEC_INIT_DECIMAL64: i32 = 64;
pub const DEC_INIT_DECSINGLE: i32 = 32;
pub const DEC_INIT_DECIMAL128: i32 = 128;
pub const DEC_INIT_DECDOUBLE: i32 = 64;
pub const DEC_INIT_DECQUAD: i32 = 128;

pub const DEC_Conversion_syntax: u32 = 0x00000001;
pub const DEC_Division_by_zero: u32 = 0x00000002;
pub const DEC_Division_impossible: u32 = 0x00000004;
pub const DEC_Division_undefined: u32 = 0x00000008;
pub const DEC_Insufficient_storage: u32 = 0x00000010;
pub const DEC_Inexact: u32 = 0x00000020;
pub const DEC_Invalid_context: u32 = 0x00000040;
pub const DEC_Invalid_operation: u32 = 0x00000080;
pub const DEC_Overflow: u32 = 0x00000200;
pub const DEC_Clamped: u32 = 0x00000400;
pub const DEC_Rounded: u32 = 0x00000800;
pub const DEC_Subnormal: u32 = 0x00001000;
pub const DEC_Underflow: u32 = 0x00002000;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct decContext {
    pub digits: i32,
    pub emax: i32,
    pub emin: i32,
    pub round: rounding,
    pub traps: u32,
    pub status: u32,
    pub clamp: u8,
}

extern "C" {
    pub fn decContextClearStatus(arg1: *mut decContext, arg2: u32) -> *mut decContext;
    pub fn decContextDefault(arg1: *mut decContext, arg2: i32) -> *mut decContext;
    pub fn decContextGetRounding(arg1: *mut decContext) -> rounding;
    pub fn decContextGetStatus(arg1: *mut decContext) -> u32;
    pub fn decContextRestoreStatus(arg1: *mut decContext, arg2: u32, arg3: u32) -> *mut decContext;
    pub fn decContextSaveStatus(arg1: *mut decContext, arg2: u32) -> u32;
    pub fn decContextSetRounding(arg1: *mut decContext, arg2: rounding) -> *mut decContext;
    pub fn decContextSetStatus(arg1: *mut decContext, arg2: u32) -> *mut decContext;
    pub fn decContextSetStatusFromString(
        arg1: *mut decContext,
        arg2: *const c_char,
    ) -> *mut decContext;
    pub fn decContextSetStatusFromStringQuiet(
        arg1: *mut decContext,
        arg2: *const c_char,
    ) -> *mut decContext;
    pub fn decContextSetStatusQuiet(arg1: *mut decContext, arg2: u32) -> *mut decContext;
    pub fn decContextStatusToString(arg1: *const decContext) -> *const c_char;
    pub fn decContextTestEndian(arg1: u8) -> i32;
    pub fn decContextTestSavedStatus(arg1: u32, arg2: u32) -> u32;
    pub fn decContextTestStatus(arg1: *mut decContext, arg2: u32) -> u32;
    pub fn decContextZeroStatus(arg1: *mut decContext) -> *mut decContext;
}

pub const DECNEG: u8 = 0x80;
pub const DECINF: u8 = 0x40;
pub const DECNAN: u8 = 0x20;
pub const DECSNAN: u8 = 0x10;
pub const DECSPECIAL: u8 = DECINF | DECNAN | DECSNAN;

pub const DECDPUN: usize = 3;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct decNumber {
    pub digits: i32,
    pub exponent: i32,
    pub bits: u8,
    pub lsu: [u16; 12usize],
}

extern "C" {
    pub fn decNumberFromInt32(arg1: *mut decNumber, arg2: i32) -> *mut decNumber;
    pub fn decNumberFromUInt32(arg1: *mut decNumber, arg2: u32) -> *mut decNumber;
    pub fn decNumberFromString(
        arg1: *mut decNumber,
        arg2: *const c_char,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberToString(arg1: *const decNumber, arg2: *mut c_char) -> *mut c_char;
    pub fn decNumberToEngString(arg1: *const decNumber, arg2: *mut c_char) -> *mut c_char;
    pub fn decNumberToUInt32(arg1: *const decNumber, arg2: *mut decContext) -> u32;
    pub fn decNumberToInt32(arg1: *const decNumber, arg2: *mut decContext) -> i32;
    pub fn decNumberGetBCD(arg1: *const decNumber, arg2: *mut u8) -> *mut u8;
    pub fn decNumberSetBCD(arg1: *mut decNumber, arg2: *const u8, arg3: u32) -> *mut decNumber;
    pub fn decNumberAbs(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberAdd(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberAnd(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberCompare(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberCompareSignal(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberCompareTotal(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberCompareTotalMag(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberDivide(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberDivideInteger(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberExp(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberFMA(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *const decNumber,
        arg5: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberInvert(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberLn(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberLogB(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberLog10(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberMax(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberMaxMag(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberMin(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberMinMag(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberMinus(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberMultiply(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberNormalize(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberOr(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberPlus(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberPower(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberQuantize(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberReduce(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberRemainder(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberRemainderNear(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberRescale(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberRotate(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberSameQuantum(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
    ) -> *mut decNumber;
    pub fn decNumberScaleB(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberShift(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberSquareRoot(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberSubtract(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberToIntegralExact(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberToIntegralValue(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberXor(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberClass(arg1: *const decNumber, arg2: *mut decContext) -> decClass;
    pub fn decNumberClassToString(arg1: decClass) -> *const c_char;
    pub fn decNumberCopy(arg1: *mut decNumber, arg2: *const decNumber) -> *mut decNumber;
    pub fn decNumberCopyAbs(arg1: *mut decNumber, arg2: *const decNumber) -> *mut decNumber;
    pub fn decNumberCopyNegate(arg1: *mut decNumber, arg2: *const decNumber) -> *mut decNumber;
    pub fn decNumberCopySign(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
    ) -> *mut decNumber;
    pub fn decNumberNextMinus(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberNextPlus(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberNextToward(
        arg1: *mut decNumber,
        arg2: *const decNumber,
        arg3: *const decNumber,
        arg4: *mut decContext,
    ) -> *mut decNumber;
    pub fn decNumberTrim(arg1: *mut decNumber) -> *mut decNumber;
    pub fn decNumberVersion() -> *const c_char;
    pub fn decNumberZero(arg1: *mut decNumber) -> *mut decNumber;
    pub fn decNumberIsNormal(arg1: *const decNumber, arg2: *mut decContext) -> i32;
    pub fn decNumberIsSubnormal(arg1: *const decNumber, arg2: *mut decContext) -> i32;
}

pub const DECSINGLE_Bytes: usize = 4;
pub const DECSINGLE_Pmax: usize = 7;
pub const DECSINGLE_Emin: isize = -95;
pub const DECSINGLE_Emax: usize = 96;
pub const DECSINGLE_EmaxD: usize = 3;
pub const DECSINGLE_Bias: usize = 101;
pub const DECSINGLE_String: usize = 16;
pub const DECSINGLE_EconL: usize = 6;
pub const DECSINGLE_Declets: usize = 2;
pub const DECSINGLE_Ehigh: usize = DECSINGLE_Emax + DECSINGLE_Bias - (DECSINGLE_Pmax - 1);

pub type decSingle = decimal32;

extern "C" {
    pub fn decSingleFromBCD(
        arg1: *mut decSingle,
        arg2: i32,
        arg3: *const u8,
        arg4: i32,
    ) -> *mut decSingle;
    pub fn decSingleFromPacked(arg1: *mut decSingle, arg2: i32, arg3: *const u8) -> *mut decSingle;
    pub fn decSingleFromPackedChecked(
        arg1: *mut decSingle,
        arg2: i32,
        arg3: *const u8,
    ) -> *mut decSingle;
    pub fn decSingleFromString(
        arg1: *mut decSingle,
        arg2: *const c_char,
        arg3: *mut decContext,
    ) -> *mut decSingle;
    pub fn decSingleFromWider(
        arg1: *mut decSingle,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decSingle;
    pub fn decSingleGetCoefficient(arg1: *const decSingle, arg2: *mut u8) -> i32;
    pub fn decSingleGetExponent(arg1: *const decSingle) -> i32;
    pub fn decSingleSetCoefficient(
        arg1: *mut decSingle,
        arg2: *const u8,
        arg3: i32,
    ) -> *mut decSingle;
    pub fn decSingleSetExponent(
        arg1: *mut decSingle,
        arg2: *mut decContext,
        arg3: i32,
    ) -> *mut decSingle;
    pub fn decSingleShow(arg1: *const decSingle, arg2: *const c_char);
    pub fn decSingleToBCD(arg1: *const decSingle, arg2: *mut i32, arg3: *mut u8) -> i32;
    pub fn decSingleToEngString(arg1: *const decSingle, arg2: *mut c_char) -> *mut c_char;
    pub fn decSingleToPacked(arg1: *const decSingle, arg2: *mut i32, arg3: *mut u8) -> i32;
    pub fn decSingleToString(arg1: *const decSingle, arg2: *mut c_char) -> *mut c_char;
    pub fn decSingleToWider(arg1: *const decSingle, arg2: *mut decDouble) -> *mut decDouble;
    pub fn decSingleZero(arg1: *mut decSingle) -> *mut decSingle;
    pub fn decSingleRadix(arg1: *const decSingle) -> u32;
    pub fn decSingleVersion() -> *const c_char;
}

pub const DECDOUBLE_Bytes: usize = 8;
pub const DECDOUBLE_Pmax: usize = 16;
pub const DECDOUBLE_Emin: isize = -383;
pub const DECDOUBLE_Emax: usize = 384;
pub const DECDOUBLE_EmaxD: usize = 3;
pub const DECDOUBLE_Bias: usize = 398;
pub const DECDOUBLE_String: usize = 25;
pub const DECDOUBLE_EconL: usize = 8;
pub const DECDOUBLE_Declets: usize = 5;
pub const DECDOUBLE_Ehigh: usize = DECDOUBLE_Emax + DECDOUBLE_Bias - (DECDOUBLE_Pmax - 1);

pub type decDouble = decimal64;

extern "C" {
    pub fn decDoubleFromBCD(
        arg1: *mut decDouble,
        arg2: i32,
        arg3: *const u8,
        arg4: i32,
    ) -> *mut decDouble;
    pub fn decDoubleFromInt32(arg1: *mut decDouble, arg2: i32) -> *mut decDouble;
    pub fn decDoubleFromPacked(arg1: *mut decDouble, arg2: i32, arg3: *const u8) -> *mut decDouble;
    pub fn decDoubleFromPackedChecked(
        arg1: *mut decDouble,
        arg2: i32,
        arg3: *const u8,
    ) -> *mut decDouble;
    pub fn decDoubleFromString(
        arg1: *mut decDouble,
        arg2: *const c_char,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleFromUInt32(arg1: *mut decDouble, arg2: u32) -> *mut decDouble;
    pub fn decDoubleFromWider(
        arg1: *mut decDouble,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleGetCoefficient(arg1: *const decDouble, arg2: *mut u8) -> i32;
    pub fn decDoubleGetExponent(arg1: *const decDouble) -> i32;
    pub fn decDoubleSetCoefficient(
        arg1: *mut decDouble,
        arg2: *const u8,
        arg3: i32,
    ) -> *mut decDouble;
    pub fn decDoubleSetExponent(
        arg1: *mut decDouble,
        arg2: *mut decContext,
        arg3: i32,
    ) -> *mut decDouble;
    pub fn decDoubleShow(arg1: *const decDouble, arg2: *const c_char);
    pub fn decDoubleToBCD(arg1: *const decDouble, arg2: *mut i32, arg3: *mut u8) -> i32;
    pub fn decDoubleToEngString(arg1: *const decDouble, arg2: *mut c_char) -> *mut c_char;
    pub fn decDoubleToInt32(arg1: *const decDouble, arg2: *mut decContext, arg3: rounding) -> i32;
    pub fn decDoubleToInt32Exact(
        arg1: *const decDouble,
        arg2: *mut decContext,
        arg3: rounding,
    ) -> i32;
    pub fn decDoubleToPacked(arg1: *const decDouble, arg2: *mut i32, arg3: *mut u8) -> i32;
    pub fn decDoubleToString(arg1: *const decDouble, arg2: *mut c_char) -> *mut c_char;
    pub fn decDoubleToUInt32(arg1: *const decDouble, arg2: *mut decContext, arg3: rounding) -> u32;
    pub fn decDoubleToUInt32Exact(
        arg1: *const decDouble,
        arg2: *mut decContext,
        arg3: rounding,
    ) -> u32;
    pub fn decDoubleToWider(arg1: *const decDouble, arg2: *mut decQuad) -> *mut decQuad;
    pub fn decDoubleZero(arg1: *mut decDouble) -> *mut decDouble;
    pub fn decDoubleAbs(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleAdd(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleAnd(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleDivide(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleDivideInteger(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleFMA(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *const decDouble,
        arg5: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleInvert(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleLogB(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleMax(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleMaxMag(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleMin(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleMinMag(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleMinus(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleMultiply(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleNextMinus(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleNextPlus(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleNextToward(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleOr(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoublePlus(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleQuantize(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleReduce(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleRemainder(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleRemainderNear(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleRotate(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleScaleB(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleShift(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleSubtract(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleToIntegralValue(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
        arg4: rounding,
    ) -> *mut decDouble;
    pub fn decDoubleToIntegralExact(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleXor(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleCompare(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleCompareSignal(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
        arg4: *mut decContext,
    ) -> *mut decDouble;
    pub fn decDoubleCompareTotal(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
    ) -> *mut decDouble;
    pub fn decDoubleCompareTotalMag(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
    ) -> *mut decDouble;
    pub fn decDoubleCanonical(arg1: *mut decDouble, arg2: *const decDouble) -> *mut decDouble;
    pub fn decDoubleCopy(arg1: *mut decDouble, arg2: *const decDouble) -> *mut decDouble;
    pub fn decDoubleCopyAbs(arg1: *mut decDouble, arg2: *const decDouble) -> *mut decDouble;
    pub fn decDoubleCopyNegate(arg1: *mut decDouble, arg2: *const decDouble) -> *mut decDouble;
    pub fn decDoubleCopySign(
        arg1: *mut decDouble,
        arg2: *const decDouble,
        arg3: *const decDouble,
    ) -> *mut decDouble;
    pub fn decDoubleClass(arg1: *const decDouble) -> decClass;
    pub fn decDoubleClassString(arg1: *const decDouble) -> *const c_char;
    pub fn decDoubleDigits(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsCanonical(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsFinite(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsInfinite(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsInteger(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsLogical(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsNaN(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsNegative(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsNormal(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsPositive(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsSignaling(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsSignalling(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsSigned(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsSubnormal(arg1: *const decDouble) -> u32;
    pub fn decDoubleIsZero(arg1: *const decDouble) -> u32;
    pub fn decDoubleRadix(arg1: *const decDouble) -> u32;
    pub fn decDoubleSameQuantum(arg1: *const decDouble, arg2: *const decDouble) -> u32;
    pub fn decDoubleVersion() -> *const c_char;
}

pub const DECQUAD_Bytes: usize = 16;
pub const DECQUAD_Pmax: usize = 34;
pub const DECQUAD_Emin: isize = -6143;
pub const DECQUAD_Emax: usize = 6144;
pub const DECQUAD_EmaxD: usize = 4;
pub const DECQUAD_Bias: usize = 6176;
pub const DECQUAD_String: usize = 43;
pub const DECQUAD_EconL: usize = 12;
pub const DECQUAD_Declets: usize = 11;
pub const DECQUAD_Ehigh: usize = DECQUAD_Emax + DECQUAD_Bias - (DECQUAD_Pmax - 1);

pub type decQuad = decimal128;

extern "C" {
    pub fn decQuadFromBCD(
        arg1: *mut decQuad,
        arg2: i32,
        arg3: *const u8,
        arg4: i32,
    ) -> *mut decQuad;
    pub fn decQuadFromInt32(arg1: *mut decQuad, arg2: i32) -> *mut decQuad;
    pub fn decQuadFromPacked(arg1: *mut decQuad, arg2: i32, arg3: *const u8) -> *mut decQuad;
    pub fn decQuadFromPackedChecked(arg1: *mut decQuad, arg2: i32, arg3: *const u8)
        -> *mut decQuad;
    pub fn decQuadFromString(
        arg1: *mut decQuad,
        arg2: *const c_char,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadFromUInt32(arg1: *mut decQuad, arg2: u32) -> *mut decQuad;
    pub fn decQuadGetCoefficient(arg1: *const decQuad, arg2: *mut u8) -> i32;
    pub fn decQuadGetExponent(arg1: *const decQuad) -> i32;
    pub fn decQuadSetCoefficient(arg1: *mut decQuad, arg2: *const u8, arg3: i32) -> *mut decQuad;
    pub fn decQuadSetExponent(arg1: *mut decQuad, arg2: *mut decContext, arg3: i32)
        -> *mut decQuad;
    pub fn decQuadShow(arg1: *const decQuad, arg2: *const c_char);
    pub fn decQuadToBCD(arg1: *const decQuad, arg2: *mut i32, arg3: *mut u8) -> i32;
    pub fn decQuadToEngString(arg1: *const decQuad, arg2: *mut c_char) -> *mut c_char;
    pub fn decQuadToInt32(arg1: *const decQuad, arg2: *mut decContext, arg3: rounding) -> i32;
    pub fn decQuadToInt32Exact(arg1: *const decQuad, arg2: *mut decContext, arg3: rounding) -> i32;
    pub fn decQuadToPacked(arg1: *const decQuad, arg2: *mut i32, arg3: *mut u8) -> i32;
    pub fn decQuadToString(arg1: *const decQuad, arg2: *mut c_char) -> *mut c_char;
    pub fn decQuadToUInt32(arg1: *const decQuad, arg2: *mut decContext, arg3: rounding) -> u32;
    pub fn decQuadToUInt32Exact(arg1: *const decQuad, arg2: *mut decContext, arg3: rounding)
        -> u32;
    pub fn decQuadZero(arg1: *mut decQuad) -> *mut decQuad;
    pub fn decQuadAbs(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadAdd(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadAnd(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadDivide(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadDivideInteger(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadFMA(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *const decQuad,
        arg5: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadInvert(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadLogB(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadMax(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadMaxMag(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadMin(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadMinMag(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadMinus(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadMultiply(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadNextMinus(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadNextPlus(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadNextToward(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadOr(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadPlus(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadQuantize(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadReduce(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadRemainder(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadRemainderNear(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadRotate(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadScaleB(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadShift(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadSubtract(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadToIntegralValue(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
        arg4: rounding,
    ) -> *mut decQuad;
    pub fn decQuadToIntegralExact(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadXor(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadCompare(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadCompareSignal(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
        arg4: *mut decContext,
    ) -> *mut decQuad;
    pub fn decQuadCompareTotal(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
    ) -> *mut decQuad;
    pub fn decQuadCompareTotalMag(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
    ) -> *mut decQuad;
    pub fn decQuadCanonical(arg1: *mut decQuad, arg2: *const decQuad) -> *mut decQuad;
    pub fn decQuadCopy(arg1: *mut decQuad, arg2: *const decQuad) -> *mut decQuad;
    pub fn decQuadCopyAbs(arg1: *mut decQuad, arg2: *const decQuad) -> *mut decQuad;
    pub fn decQuadCopyNegate(arg1: *mut decQuad, arg2: *const decQuad) -> *mut decQuad;
    pub fn decQuadCopySign(
        arg1: *mut decQuad,
        arg2: *const decQuad,
        arg3: *const decQuad,
    ) -> *mut decQuad;
    pub fn decQuadClass(arg1: *const decQuad) -> decClass;
    pub fn decQuadClassString(arg1: *const decQuad) -> *const c_char;
    pub fn decQuadDigits(arg1: *const decQuad) -> u32;
    pub fn decQuadIsCanonical(arg1: *const decQuad) -> u32;
    pub fn decQuadIsFinite(arg1: *const decQuad) -> u32;
    pub fn decQuadIsInteger(arg1: *const decQuad) -> u32;
    pub fn decQuadIsLogical(arg1: *const decQuad) -> u32;
    pub fn decQuadIsInfinite(arg1: *const decQuad) -> u32;
    pub fn decQuadIsNaN(arg1: *const decQuad) -> u32;
    pub fn decQuadIsNegative(arg1: *const decQuad) -> u32;
    pub fn decQuadIsNormal(arg1: *const decQuad) -> u32;
    pub fn decQuadIsPositive(arg1: *const decQuad) -> u32;
    pub fn decQuadIsSignaling(arg1: *const decQuad) -> u32;
    pub fn decQuadIsSignalling(arg1: *const decQuad) -> u32;
    pub fn decQuadIsSigned(arg1: *const decQuad) -> u32;
    pub fn decQuadIsSubnormal(arg1: *const decQuad) -> u32;
    pub fn decQuadIsZero(arg1: *const decQuad) -> u32;
    pub fn decQuadRadix(arg1: *const decQuad) -> u32;
    pub fn decQuadSameQuantum(arg1: *const decQuad, arg2: *const decQuad) -> u32;
    pub fn decQuadVersion() -> *const c_char;
}

#[repr(C, align(4))]
#[derive(Debug, Copy, Clone)]
pub struct decimal32 {
    pub bytes: [u8; 4usize],
}

extern "C" {
    pub fn decimal32FromString(
        arg1: *mut decimal32,
        arg2: *const c_char,
        arg3: *mut decContext,
    ) -> *mut decimal32;
    pub fn decimal32ToString(arg1: *const decimal32, arg2: *mut c_char) -> *mut c_char;
    pub fn decimal32ToEngString(arg1: *const decimal32, arg2: *mut c_char) -> *mut c_char;
    pub fn decimal32FromNumber(
        arg1: *mut decimal32,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decimal32;
    pub fn decimal32ToNumber(arg1: *const decimal32, arg2: *mut decNumber) -> *mut decNumber;
    pub fn decimal32IsCanonical(arg1: *const decimal32) -> u32;
    pub fn decimal32Canonical(arg1: *mut decimal32, arg2: *const decimal32) -> *mut decimal32;
    pub fn decPackedFromNumber(
        arg1: *mut u8,
        arg2: i32,
        arg3: *mut i32,
        arg4: *const decNumber,
    ) -> *mut u8;
    pub fn decPackedToNumber(
        arg1: *const u8,
        arg2: i32,
        arg3: *const i32,
        arg4: *mut decNumber,
    ) -> *mut decNumber;
}

#[repr(C, align(4))]
#[derive(Debug, Copy, Clone)]
pub struct decimal64 {
    pub bytes: [u8; 8usize],
}

extern "C" {
    pub fn decimal64FromString(
        arg1: *mut decimal64,
        arg2: *const c_char,
        arg3: *mut decContext,
    ) -> *mut decimal64;
    pub fn decimal64ToString(arg1: *const decimal64, arg2: *mut c_char) -> *mut c_char;
    pub fn decimal64ToEngString(arg1: *const decimal64, arg2: *mut c_char) -> *mut c_char;
    pub fn decimal64FromNumber(
        arg1: *mut decimal64,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decimal64;
    pub fn decimal64ToNumber(arg1: *const decimal64, arg2: *mut decNumber) -> *mut decNumber;
    pub fn decimal64IsCanonical(arg1: *const decimal64) -> u32;
    pub fn decimal64Canonical(arg1: *mut decimal64, arg2: *const decimal64) -> *mut decimal64;
}

#[repr(C, align(4))]
#[derive(Debug, Copy, Clone)]
pub struct decimal128 {
    pub bytes: [u8; 16usize],
}

extern "C" {
    pub fn decimal128FromString(
        arg1: *mut decimal128,
        arg2: *const c_char,
        arg3: *mut decContext,
    ) -> *mut decimal128;
    pub fn decimal128ToString(arg1: *const decimal128, arg2: *mut c_char) -> *mut c_char;
    pub fn decimal128ToEngString(arg1: *const decimal128, arg2: *mut c_char) -> *mut c_char;
    pub fn decimal128FromNumber(
        arg1: *mut decimal128,
        arg2: *const decNumber,
        arg3: *mut decContext,
    ) -> *mut decimal128;
    pub fn decimal128ToNumber(arg1: *const decimal128, arg2: *mut decNumber) -> *mut decNumber;
    pub fn decimal128IsCanonical(arg1: *const decimal128) -> u32;
    pub fn decimal128Canonical(arg1: *mut decimal128, arg2: *const decimal128) -> *mut decimal128;
}

/// Constants used for efficiently decoding decimal coefficients.
extern "C" {
    pub static DPD2BIN: [u16; 1024];
    pub static DPD2BINK: [u32; 1024];
    pub static DPD2BINM: [u32; 1024];
    pub static DECCOMBMSD: [u32; 64];
    pub static BIN2CHAR: [u8; 4001];
}

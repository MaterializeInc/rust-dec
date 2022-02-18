#[macro_export]
/// A macro to construct a [`Decimal32`] from a literal.
/// Converts the input tokens to a string, and then parses the string into a [`Decimal32`].
/// Panics if the provided input is not a valid [`Decimal32`] literal.
///
/// [`Decimal32`]: crate::Decimal32
/// 
/// # Examples:
/// ```
/// use dec::d32;
///
/// assert!(d32!(1.753).to_string() == "1.753");
/// ```
macro_rules! d32 {
    ($l:expr) => {
        <$crate::Decimal32 as ::std::str::FromStr>::from_str(stringify!($l))
            .unwrap_or_else(|e| panic!("{}", e.to_string()))
    };
}

#[macro_export]
/// A macro to construct a [`Decimal64`] from a literal.
/// Converts the input tokens to a string, and then parses the string into a [`Decimal64`].
/// Panics if the provided input is not a valid [`Decimal64`] literal.
///
/// [`Decimal64`]: crate::Decimal64
/// 
/// # Examples:
/// ```
/// use dec::d64;
///
/// assert!(d64!(NaN).is_nan());
/// assert!(d64!(0).is_zero());
/// assert!(d64!(-0.1).is_negative());
/// ```
macro_rules! d64 {
    ($l:expr) => {
        <$crate::Decimal64 as ::std::str::FromStr>::from_str(stringify!($l))
            .unwrap_or_else(|e| panic!("{}", e.to_string()))
    };
}

#[macro_export]
///A macro to construct a [`Decimal128`] from a literal.
/// Converts the input tokens to a string, and then parses the string into a [`Decimal128`].
/// Panics if the provided input is not a valid [`Decimal128`] literal.
///
/// [`Decimal128`]: crate::Decimal128
/// 
/// # Examples:
/// ```
/// use dec::d128;
///
/// assert!(d128!(NaN).is_nan());
/// assert!(d128!(0).is_zero());
/// assert!(d128!(-0.1).is_negative());
/// ```
macro_rules! d128 {
    ($l:expr) => {
        <$crate::Decimal128 as ::std::str::FromStr>::from_str(stringify!($l))
            .unwrap_or_else(|e| panic!("{}", e.to_string()))
    };
}

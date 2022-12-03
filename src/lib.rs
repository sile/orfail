//! An error handling library for portable unrecoverable errors.
//!
//! This crate provides,
//!
//! - [`Failure`] struct that represents an unrecoverable error with an error code, message and user-level backtrace
//!   - Error code and message are optional
//!   - Constituted with simple types ([`u32`], [`String`], and [`Vec`] of those)
//!     - Portable across process and language boundaries
//!     - Optional [`serde`] support ("serde" feature)
//!   - Doesn't implement [`std::error::Error`] trait
//! - [`OrFail`] trait
//!   - Backtrace location is appended to [`Failure`] each time when calling [`OrFail::or_fail()`]
//!   - [`bool`], [`Option<_>`] and [`Result<_, _>`](std::result::Result) implement [`OrFail`]
//!
//! # Examples
//!
//! ```
//! use orfail::{OrFail, Result};
//!
//! fn check_non_zero(n: isize) -> Result<()> {
//!     (n != 0).or_fail()?;
//!     Ok(())
//! }
//!
//! fn safe_div(x: isize, y: isize) -> Result<isize> {
//!     check_non_zero(y).or_fail()?;
//!     Ok(x / y)
//! }
//!
//! // OK
//! assert_eq!(safe_div(4, 2), Ok(2));
//!
//! // NG
//! assert_eq!(safe_div(4, 0).err().map(|e| e.to_string()),
//!            Some(
//! r#"failed due to "expected `true` but got `false`"
//!   at src/lib.rs:7
//!   at src/lib.rs:12
//! "#.to_owned()));
//! ```
#![warn(missing_docs)]
use std::marker::PhantomData;

/// This trait allows for returning an error code held by [`Failure`].
pub trait ErrorCode {
    /// Returns an error code representing this instance.
    fn error_code(&self) -> u32;

    /// Takes an error code and returns a message describing the code if possible.
    #[allow(unused_variables)]
    fn default_message(code: u32) -> Option<String> {
        None
    }
}

impl ErrorCode for u32 {
    fn error_code(&self) -> u32 {
        *self
    }
}

/// A marker trait representing that `C` can be converted into the type implementing this trait.
pub trait TakeOver<C: ErrorCode>: ErrorCode {}

impl<C: ErrorCode> TakeOver<C> for u32 {}

/// This crate specific [`Result`](std::result::Result) type.
pub type Result<T, C = u32> = std::result::Result<T, Failure<C>>;

/// [`Failure`] typically represents an unrecoverable error with an error code, message, and backtrace.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Failure<C = u32> {
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    /// Error code.
    pub code: Option<u32>,

    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    /// Error message.
    pub message: Option<String>,

    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    /// Backtrace.
    pub backtrace: Vec<Location>,

    #[cfg_attr(feature = "serde", serde(skip))]
    _code_type: PhantomData<C>,
}

impl<C: ErrorCode> Failure<C> {
    /// Makes a new [`Failure`] instance whose backtrace contains the current caller location.
    #[track_caller]
    pub fn new() -> Self {
        Self::default()
    }

    /// Updates the error code of this [`Failure`] instance.
    ///
    /// If the error message of this instance is `None` and `C::default_message(code.error_code())` returns `Some(_)`,
    /// the default message is set to the [`Failure::message`](#structfield.message) field.
    pub fn code(mut self, code: C) -> Self {
        self.code = Some(code.error_code());
        if self.message.is_none() {
            self.message = C::default_message(code.error_code());
        }
        self
    }

    /// Updates the error message of this [`Failure`] instance.
    pub fn message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }
}

impl<C: ErrorCode> Default for Failure<C> {
    #[track_caller]
    fn default() -> Self {
        Self {
            code: None,
            message: None,
            backtrace: vec![Location::new()],
            _code_type: PhantomData,
        }
    }
}

impl<C: ErrorCode> std::fmt::Debug for Failure<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl<C: ErrorCode> std::fmt::Display for Failure<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "failed")?;
        if let Some(code) = self.code {
            write!(f, " with error code '{code}'")?;
        }
        if let Some(message) = &self.message {
            write!(f, " due to {message:?}")?;
        } else if let Some(message) = self.code.and_then(C::default_message) {
            write!(f, " due to {message:?}")?;
        }
        writeln!(f)?;
        for location in &self.backtrace {
            writeln!(f, "  at {}:{}", location.file, location.line)?;
        }
        Ok(())
    }
}

/// A location in the backtrace of a [`Failure`] instance.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Location {
    /// File name.
    pub file: String,

    /// Line number.
    pub line: u32,
}

impl Location {
    /// Makes a new [`Location`] instance containing the caller's file name and line number.
    #[track_caller]
    pub fn new() -> Self {
        let location = std::panic::Location::caller();
        Self {
            file: location.file().to_owned(),
            line: location.line(),
        }
    }
}

impl Default for Location {
    #[track_caller]
    fn default() -> Self {
        Self::new()
    }
}

/// This trait allows for converting a value into `Result<_, Failure>`.
pub trait OrFail<C: ErrorCode>: Sized {
    /// Success value type (used for the `Ok(_)` variant).
    type Value;

    /// Error value type (used for the `Err(_)` variant).
    type Error;

    /// Returns `Err(Failure<C>)` if `self` is a failure value.
    ///
    /// If `Err(_)` is returned, this method should add the current caller location to the backtrace of the resulting `Failure<C>`.
    fn or_fail(self) -> Result<Self::Value, C>;
}

impl<C: ErrorCode> OrFail<C> for bool {
    type Value = ();
    type Error = ();

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, C> {
        if self {
            Ok(())
        } else {
            Err(Failure::new().message("expected `true` but got `false`"))
        }
    }
}

impl<T, C: ErrorCode> OrFail<C> for Option<T> {
    type Value = T;
    type Error = ();

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, C> {
        if let Some(value) = self {
            Ok(value)
        } else {
            Err(Failure::new().message("expected `Some(_)` but got `None`"))
        }
    }
}

impl<T, E: std::error::Error, C: ErrorCode> OrFail<C> for std::result::Result<T, E> {
    type Value = T;
    type Error = E;

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, C> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(Failure::new().message(e.to_string())),
        }
    }
}

impl<T, C: ErrorCode, D: ErrorCode> OrFail<D> for std::result::Result<T, Failure<C>>
where
    D: TakeOver<C>,
{
    type Value = T;
    type Error = Failure<D>;

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, D> {
        match self {
            Ok(value) => Ok(value),
            Err(mut failure) => {
                failure.backtrace.push(Location::new());
                Err(Failure {
                    code: failure.code,
                    message: failure.message,
                    backtrace: failure.backtrace,
                    ..Default::default()
                })
            }
        }
    }
}

/// Similar to [`std::todo!()`] but returning an `Err(Failure)` instead of panicking.
#[macro_export]
macro_rules! todo {
    () => {
        return Err(Failure::new().message("not yet implemented"));
    };
}

/// Similar to [`std::unreachable!()`] but returning an `Err(Failure)` instead of panicking.
#[macro_export]
macro_rules! unreachable {
    () => {
        return Err(Failure::new().message("internal error: entered unreachable code"));
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert!((true.or_fail() as Result<_>).is_ok());
        assert!((false.or_fail() as Result<_>).is_err());

        let failure: Failure = false.or_fail().err().unwrap();
        assert!(failure.code.is_none());
        assert!(failure.message.is_some());
        assert_eq!(failure.backtrace.len(), 1);

        let failure: Failure = false
            .or_fail()
            .map_err(|f| f.code(10))
            .or_fail()
            .err()
            .unwrap();
        assert_eq!(failure.code, Some(10));
        assert!(failure.message.is_some());
        assert_eq!(failure.backtrace.len(), 2);
    }
}

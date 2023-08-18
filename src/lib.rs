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
//!   at src/lib.rs:8
//!   at src/lib.rs:13
//! "#.to_owned()));
//! ```
#![warn(missing_docs)]

/// This crate specific [`Result`](std::result::Result) type.
pub type Result<T> = std::result::Result<T, Failure>;

/// [`Failure`] typically represents an unrecoverable error with an error code, message, and backtrace.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Failure {
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
}

impl Failure {
    /// Makes a new [`Failure`] instance whose backtrace contains the current caller location.
    #[track_caller]
    pub fn new() -> Self {
        Self::default()
    }

    /// Updates the error message of this [`Failure`] instance.
    pub fn message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }
}

impl Default for Failure {
    #[track_caller]
    fn default() -> Self {
        Self {
            message: None,
            backtrace: vec![Location::new()],
        }
    }
}

impl std::fmt::Debug for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "failed")?;
        if let Some(message) = &self.message {
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
pub trait OrFail: Sized {
    /// Success value type (used for the `Ok(_)` variant).
    type Value;

    /// Returns `Err(Failure<C>)` if `self` is a failure value.
    ///
    /// If `Err(_)` is returned, this method should add the current caller location to the backtrace of the resulting `Failure<C>`.
    fn or_fail(self) -> Result<Self::Value>;
}

impl OrFail for bool {
    type Value = ();

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value> {
        if self {
            Ok(())
        } else {
            Err(Failure::new().message("expected `true` but got `false`"))
        }
    }
}

impl<T> OrFail for Option<T> {
    type Value = T;

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value> {
        if let Some(value) = self {
            Ok(value)
        } else {
            Err(Failure::new().message("expected `Some(_)` but got `None`"))
        }
    }
}

impl<T, E: std::error::Error> OrFail for std::result::Result<T, E> {
    type Value = T;

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(Failure::new().message(e.to_string())),
        }
    }
}

impl<T> OrFail for Result<T> {
    type Value = T;

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value> {
        match self {
            Ok(value) => Ok(value),
            Err(mut failure) => {
                failure.backtrace.push(Location::new());
                Err(Failure {
                    message: failure.message,
                    backtrace: failure.backtrace,
                })
            }
        }
    }
}

/// Similar to [`std::todo!()`] but returning an `Err(Failure)` instead of panicking.
#[macro_export]
macro_rules! todo {
    () => {
        return Err($crate::Failure::new().message("not yet implemented"));
    };
}

/// Similar to [`std::unreachable!()`] but returning an `Err(Failure)` instead of panicking.
#[macro_export]
macro_rules! unreachable {
    () => {
        return Err($crate::Failure::new().message("internal error: entered unreachable code"));
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
        assert!(failure.message.is_some());
        assert_eq!(failure.backtrace.len(), 1);

        let failure: Failure = false.or_fail().or_fail().err().unwrap();
        assert!(failure.message.is_some());
        assert_eq!(failure.backtrace.len(), 2);
    }
}

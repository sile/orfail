use std::marker::PhantomData;

pub trait ErrorCode {
    fn error_code(&self) -> u32;

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

pub trait TakeOver<C: ErrorCode>: ErrorCode {}

impl<C: ErrorCode> TakeOver<C> for u32 {}

pub type Result<T, C = u32> = std::result::Result<T, Failure<C>>;

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Failure<C = u32> {
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub code: Option<u32>,

    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub message: Option<String>,

    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub backtrace: Vec<Location>,

    #[cfg_attr(feature = "serde", serde(skip))]
    _code_type: PhantomData<C>,
}

impl<C: ErrorCode> Failure<C> {
    #[track_caller]
    pub fn new(code: C, message: impl Into<String>) -> Self {
        Self {
            code: Some(code.error_code()),
            message: Some(message.into()),
            ..Default::default()
        }
    }

    #[track_caller]
    pub fn with_code(code: C) -> Self {
        let code = code.error_code();
        Self {
            code: Some(code),
            message: C::default_message(code),
            ..Default::default()
        }
    }

    #[track_caller]
    pub fn with_message(message: impl Into<String>) -> Self {
        Self {
            message: Some(message.into()),
            ..Default::default()
        }
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Location {
    pub file: String,
    pub line: u32,
}

impl Location {
    #[track_caller]
    pub fn new() -> Self {
        let location = std::panic::Location::caller();
        Self {
            file: location.file().to_owned(),
            line: location.line(),
        }
    }
}

pub trait OrFail<C: ErrorCode>: Sized {
    type Value;
    type Error;

    fn or_fail(self) -> Result<Self::Value, C>;

    fn or_fail_with(self, f: impl FnOnce(Self::Error) -> Failure<C>) -> Result<Self::Value, C>;
}

impl<C: ErrorCode> OrFail<C> for bool {
    type Value = ();
    type Error = ();

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, C> {
        self.or_fail_with(|()| Failure::with_message("expected `true` but got `false`"))
    }

    #[track_caller]
    fn or_fail_with(self, f: impl FnOnce(Self::Error) -> Failure<C>) -> Result<Self::Value, C> {
        if self {
            Ok(())
        } else {
            Err(f(()))
        }
    }
}

impl<T, C: ErrorCode> OrFail<C> for Option<T> {
    type Value = T;
    type Error = ();

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, C> {
        self.or_fail_with(|()| Failure::with_message("expected `Some(_)` but got `None`"))
    }

    #[track_caller]
    fn or_fail_with(self, f: impl FnOnce(Self::Error) -> Failure<C>) -> Result<Self::Value, C> {
        if let Some(value) = self {
            Ok(value)
        } else {
            Err(f(()))
        }
    }
}

impl<T, E: std::error::Error, C: ErrorCode> OrFail<C> for std::result::Result<T, E> {
    type Value = T;
    type Error = E;

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, C> {
        self.map_err(|e| Failure::with_message(e.to_string()))
    }

    #[track_caller]
    fn or_fail_with(self, f: impl FnOnce(Self::Error) -> Failure<C>) -> Result<Self::Value, C> {
        self.map_err(f)
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

    #[track_caller]
    fn or_fail_with(self, f: impl FnOnce(Self::Error) -> Failure<D>) -> Result<Self::Value, D> {
        self.or_fail().map_err(f)
    }
}

/// Similiar to [`std::todo!()`] but returning an `Err(Failure)` instead of panicking.
#[macro_export]
macro_rules! todo {
    () => {
        return Err(Failure::new().message("not yet implemented"));
    };
}

/// Similiar to [`std::unreachable!()`] but returning an `Err(Failure)` instead of panicking.
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
            .or_fail_with(|_| Failure::with_code(10))
            .or_fail()
            .err()
            .unwrap();
        assert_eq!(failure.code, Some(10));
        assert!(failure.message.is_none());
        assert_eq!(failure.backtrace.len(), 2);
    }
}

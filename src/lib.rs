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
    pub fn new() -> Self {
        Self {
            code: None,
            message: None,
            backtrace: vec![Location::new()],
            _code_type: PhantomData,
        }
    }

    pub fn code<D: ErrorCode>(self, code: D) -> Failure<D> {
        let code = code.error_code();
        Failure {
            code: Some(code),
            message: self.message.or_else(|| D::default_message(code)),
            backtrace: self.backtrace,
            _code_type: PhantomData,
        }
    }

    pub fn message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }
}

impl<C: ErrorCode> Default for Failure<C> {
    #[track_caller]
    fn default() -> Self {
        Self::new()
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

    fn or_fail(self) -> Result<Self::Value, C>;

    fn or_fail_with<D: ErrorCode>(
        self,
        f: impl FnOnce(Failure<C>) -> Failure<D>,
    ) -> Result<Self::Value, D> {
        self.or_fail().map_err(f)
    }
}

impl<C: ErrorCode> OrFail<C> for bool {
    type Value = ();

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

    #[track_caller]
    fn or_fail(self) -> Result<Self::Value, C> {
        self.map_err(|e| Failure::new().message(e.to_string()))
    }
}

impl<T, C: ErrorCode, D: ErrorCode> OrFail<D> for Result<T, C>
where
    D: TakeOver<C>,
{
    type Value = T;

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

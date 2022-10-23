orfail
======

[![orfail](https://img.shields.io/crates/v/orfail.svg)](https://crates.io/crates/orfail)
[![Documentation](https://docs.rs/orfail/badge.svg)](https://docs.rs/orfail)
[![Actions Status](https://github.com/sile/orfail/workflows/CI/badge.svg)](https://github.com/sile/orfail/actions)
![License](https://img.shields.io/crates/l/orfail)

An error handling library for portable unrecoverable errors.

This crate provides,

- [`Failure`] struct that represents an unrecoverable error with an error code, message and user-level backtrace
  - Error code and message are optional
  - Constituted with simple types ([`u32`], [`String`], and [`Vec`] of those)
    - Portable across process and language boundaries
    - Optional [`serde`] support ("serde" feature)
  - Doesn't implement [`std::error::Error`] trait
- [`OrFail`] trait
  - Backtrace location is appended to [`Failure`] each time when calling [`OrFail::or_fail()`]
  - [`bool`], [`Option<_>`] and [`Result<_, _>`](std::result::Result) implement [`OrFail`]

Examples
--------

```rust
use orfail::{OrFail, Result};

fn check_non_zero(n: isize) -> Result<()> {
    (n != 0).or_fail()?;
    Ok(())
}

fn safe_div(x: isize, y: isize) -> Result<isize> {
    check_non_zero(y).or_fail()?;
    Ok(x / y)
}

// OK
assert_eq!(safe_div(4, 2), Ok(2));

// NG
assert_eq!(safe_div(4, 0).err().map(|e| e.to_string()),
           Some(
r#"failed due to "expected `true` but got `false`"
  at src/lib.rs:7
  at src/lib.rs:12
"#.to_owned()));
```

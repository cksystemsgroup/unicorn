use std::any::Any;
use std::panic::{catch_unwind, AssertUnwindSafe};

use anyhow::{Error, Result};
use thiserror::Error;

#[derive(Error, Debug)]
#[error("{msg}")]
pub(crate) struct PanicError {
    msg: String,
}

pub(crate) fn try_catch<F: FnOnce() -> R, R>(panic_producer: F) -> Result<R> {
    let panic_producer = AssertUnwindSafe(panic_producer);
    match catch_unwind(panic_producer) {
        Ok(x) => Ok(x),
        Err(err) => Err(to_proper_error(&err)),
    }
}

pub(crate) fn to_proper_error(error: &(dyn Any + Send)) -> Error {
    let msg = match error.downcast_ref::<&'static str>() {
        Some(s) => *s,
        None => match error.downcast_ref::<String>() {
            Some(s) => &s[..],
            None => "Sorry, unknown payload type",
        },
    };
    let msg = msg.to_string();
    Error::from(PanicError { msg })
}

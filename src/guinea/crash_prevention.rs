use std::any::Any;
use std::mem::size_of;
use std::panic::{catch_unwind, AssertUnwindSafe};

use anyhow::{Error, Result};
use bytesize::ByteSize;
use thiserror::Error;

use unicorn::engine::system::PAGE_SIZE;
use unicorn::util::next_multiple_of;

use crate::guinea::MemoryData;
use crate::unicorn::Model;

#[derive(Error, Debug)]
#[error("{msg}")]
pub struct PanicError {
    msg: String,
}

pub fn try_catch<F: FnOnce() -> R, R>(panic_producer: F) -> Result<R> {
    let panic_producer = AssertUnwindSafe(panic_producer);
    match catch_unwind(panic_producer) {
        Ok(x) => Ok(x),
        Err(err) => Err(to_proper_error(&err)),
    }
}

pub fn fix_memory(model: &mut Model, data: &MemoryData) {
    model.data_range = data.data_start..data.data_end;
    let heap_start = next_multiple_of(data.data_end, PAGE_SIZE as u64);
    let heap_end = heap_start + data.max_heap as u64 * size_of::<u64>() as u64;
    model.heap_range = heap_start..heap_end;
    let stack_start =
        ByteSize::mib(data.memory_size).as_u64() - data.max_stack as u64 * size_of::<u64>() as u64;
    let stack_end = ByteSize::mib(data.memory_size).as_u64();
    model.stack_range = stack_start..stack_end;
    model.memory_size = ByteSize::mib(data.memory_size).as_u64();
}

pub fn to_proper_error(error: &(dyn Any + Send)) -> Error {
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

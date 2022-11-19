use crate::guinea::gui::MemoryData;
use crate::unicorn::Model;
use bytesize::ByteSize;
use std::mem::size_of;
use std::panic::{catch_unwind, UnwindSafe};
use unicorn::engine::system::PAGE_SIZE;
use unicorn::util::next_multiple_of;

pub fn unpanic<F, R, G>(panic_generator: F, if_not_panic_fn: G, error_message: &mut String)
where
    F: FnOnce() -> R + UnwindSafe,
    G: FnOnce(R),
{
    match catch_unwind(panic_generator) {
        Ok(x) => {
            if_not_panic_fn(x);
        }
        Err(err) => {
            let msg = match err.downcast_ref::<&'static str>() {
                Some(s) => *s,
                None => match err.downcast_ref::<String>() {
                    Some(s) => &s[..],
                    None => "Sorry, unknown payload type",
                },
            };

            *error_message = String::from(msg);
        }
    };
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

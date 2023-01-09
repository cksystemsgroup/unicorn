use byteorder::{ByteOrder, LittleEndian};
use std::mem::size_of;

pub const PAGE_SIZE: usize = 4 * 1024;
pub const NUMBER_OF_REGISTERS: usize = 32;

pub enum SyscallId {
    Exit = 93,
    Read = 63,
    Write = 64,
    Open = 1024,
    Openat = 56,
    Brk = 214,
    Close = 57,
    Newfstat = 80
}

// Prepares arguments on the stack like a UNIX system. Note that we
// pass an empty environment and that all strings will be properly
// zero-terminated and word-aligned:
//
// | argc | argv[0] | ... | argv[n] | 0 | env[0] | ... | env[m] | 0 |
//
pub fn prepare_unix_stack(argv: &[String], sp: u64) -> Vec<u64> {
    let mut stack = vec![];
    let argc = argv.len() as u64;
    let argv_ptrs: Vec<u64> = argv
        .iter()
        .rev()
        .map(|arg| {
            let c_string = arg.to_owned() + "\0\0\0\0\0\0\0\0";
            for chunk in c_string.as_bytes().chunks_exact(size_of::<u64>()).rev() {
                stack.push(LittleEndian::read_u64(chunk));
            }
            sp - (stack.len() * size_of::<u64>()) as u64
        })
        .collect();
    stack.push(0); // terminate env table
    stack.push(0); // terminate argv table
    for argv_ptr in argv_ptrs {
        stack.push(argv_ptr);
    }
    stack.push(argc);
    stack
}

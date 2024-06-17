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
    Newfstat = 80,
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

pub fn prepare_unix_stack32bit(argv: &[String], sp: u32) -> Vec<u64> {
    let mut stack32 = vec![];
    let argc32 = argv.len() as u32;
    let argv_ptrs32: Vec<u32> = argv
        .iter()
        .rev()
        .map(|arg| {
            let c_string = arg.to_owned() + "\0";
            for chunk in c_string.as_bytes().chunks_exact(size_of::<u32>()).rev() {
                stack32.push(LittleEndian::read_u32(chunk));
            }
            sp - (stack32.len() * size_of::<u32>()) as u32
        })
        .collect();
    stack32.push(0); // terminate env table
    stack32.push(0); // terminate argv table
    for argv_ptr in argv_ptrs32 {
        stack32.push(argv_ptr);
    }
    // Casting the 32 bit values to 64bit
    stack32.push(argc32);
    let stack: Vec<u64> = stack32.iter().map(|&x| x as u64).collect();
    stack
}

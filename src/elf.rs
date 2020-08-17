use byteorder::{ByteOrder, LittleEndian};
use goblin::elf::{
    header::header64::Header, program_header::program_header64::ProgramHeader, program_header::*,
};
use std::fs;
use std::path::Path;

/// Native page size
#[allow(dead_code)]
const PAGE_SIZE: usize = 4096;

/// Segment is writable.
#[allow(dead_code)]
const PF_W: u32 = 1 << 1;

#[allow(dead_code)]
fn extract_string(string_data: &[u8], sh_name: usize) -> &str {
    let mut len = 0;

    loop {
        let c = string_data[sh_name + len];

        if c == 0 {
            break;
        }

        len += 1;
    }

    std::str::from_utf8(&string_data[sh_name..sh_name + len])
        .expect("can not read string from elf binary")
}

/// Read raw bytes into a typed value.
trait ReadRaw {
    /// Perform the read. Unsafe because the caller needs to ensure that any bit pattern
    /// will be a valid `T`.
    unsafe fn read_raw<T: Sized + Copy>(&self) -> Option<T>;
}

impl ReadRaw for [u8] {
    unsafe fn read_raw<T: Sized + Copy>(&self) -> Option<T> {
        if self.len() < core::mem::size_of::<T>() {
            None
        } else {
            Some(*(self.as_ptr() as *const T))
        }
    }
}

/// ELF image metadata.
#[derive(Clone, Debug)]
pub struct ElfMetadata {
    /// The entry virtual address.
    pub entry_address: u64,
    pub code_length: u64,
}

pub fn load_file(object_file: &Path, memory_limit: usize) -> Option<(Vec<u8>, ElfMetadata)> {
    match fs::read(object_file) {
        Ok(buffer) => unsafe { load(buffer.as_slice(), memory_limit) },
        _ => None,
    }
}

pub unsafe fn load(image: &[u8], memory_limit: usize) -> Option<(Vec<u8>, ElfMetadata)> {
    let header: Header = match image.read_raw() {
        Some(x) => x,
        None => return None,
    };
    if header.e_phoff >= image.len() as u64 {
        return None;
    }

    let memory_in_bytes = memory_limit * 1024 * 1024;
    // let va_space = 0.. memory_in_bytes - 1;
    let mut memory: Vec<u8> = vec![0; memory_in_bytes];

    let mut segments = &image[header.e_phoff as usize..];
    for _ in 0..header.e_phnum {
        let ph: ProgramHeader = segments.read_raw()?;
        segments = &segments[core::mem::size_of::<ProgramHeader>()..];
        if ph.p_type != PT_LOAD {
            continue;
        }
        // let mut padding_before: usize = 0;
        // let start = ph.p_vaddr as usize;
        // if start % PAGE_SIZE != 0 {
        //     padding_before = start % PAGE_SIZE;
        // }
        // if ph.p_filesz > ph.p_memsz {
        //     return None;
        // }
        // let mut mem_end = start.checked_add(ph.p_memsz as usize)?;
        // let file_end = start.checked_add(ph.p_filesz as usize)?;
        // if file_end - start > image.len() {
        //     return None;
        // }
        //
        // if mem_end % PAGE_SIZE != 0 {
        //     mem_end = (mem_end / PAGE_SIZE + 1) * PAGE_SIZE;
        // }
        //
        // let va_begin = (start - padding_before).checked_add(va_space.start)?;
        // let va_end = va_begin.checked_add(mem_end - (start - padding_before))?;
        // if va_end > va_space.end {
        //     return None;
        // }

        memory[0..ph.p_filesz as usize].clone_from_slice(
            &image[(ph.p_offset as usize)..((ph.p_offset as usize) + (ph.p_filesz as usize))],
        );
    }

    // TODO: this does only work for RISCU binaries
    let code_length = match image.chunks(8).nth(15) {
        Some(chunk) => LittleEndian::read_u64(chunk),
        None => 0u64,
    };

    Some((
        memory,
        ElfMetadata {
            entry_address: header.e_entry,
            code_length,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_load_elf_binary() {
        let test_file = Path::new("division-by-zero-3-35.o");

        let _res = load_file(test_file, 10);

        // file is not generated in CI pipeline yet
        // assert!(res.is_some(), "can load ELF file");
    }
}

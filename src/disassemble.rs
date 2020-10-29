//! # Disassemble risc-v instructions

use crate::elf::load_file;
use byteorder::{ByteOrder, LittleEndian};
use riscv_decode::{
    types::{BType, IType, JType, RType, SType, UType},
    Register,
};
use std::path::Path;

use crate::decode::{Decoder, RiscU};

struct Disassembler {}

impl RiscU for Disassembler {
    fn lui(&mut self, i: UType) {
        println!("lui {:?},{:#x}", i.rd(), i.imm())
    }

    // TODO: fix representation of negativ immediate values
    fn addi(&mut self, i: IType) {
        if i.rd() == Register::Zero && i.rs1() == Register::Zero && i.imm() == 0 {
            println!("nop")
        } else {
            println!("addi {:?},{:?},{}", i.rd(), i.rs1(), i.imm())
        }
    }

    fn add(&mut self, i: RType) {
        println!("add {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn sub(&mut self, i: RType) {
        println!("sub {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn mul(&mut self, i: RType) {
        println!("mul {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn divu(&mut self, i: RType) {
        println!("divu {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn remu(&mut self, i: RType) {
        println!("remu {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn sltu(&mut self, i: RType) {
        println!("sltu {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn ld(&mut self, i: IType) {
        println!("ld {:?},{}({:?})", i.rd(), i.imm(), i.rs1())
    }

    fn sd(&mut self, i: SType) {
        println!("sd {:?},{}({:?})", i.rs2(), i.imm(), i.rs1())
    }

    fn jal(&mut self, i: JType) {
        println!("jal {:?},{}", i.rd(), i.imm())
    }

    fn jalr(&mut self, i: IType) {
        println!("jalr {:?},{}({:?})", i.rd(), i.imm(), i.rs1())
    }

    fn beq(&mut self, i: BType) {
        println!("beq {:?},{:?},{}", i.rs1(), i.rs2(), i.imm())
    }

    fn ecall(&mut self) {
        println!("ecall")
    }
}

pub fn disassemble(binary: &[u8]) {
    let mut disassembler = Disassembler {};
    let mut pipeline = Decoder::new(&mut disassembler);

    binary
        .chunks_exact(4)
        .map(LittleEndian::read_u32)
        .for_each(|x| pipeline.run(x));
}

// TODO: only tested with Selfie RISC-U file and relies on that ELF format
pub fn disassemble_riscu(file: &Path) -> Result<(), &str> {
    match load_file(file, 1024) {
        Some(program) => {
            disassemble(program.code_segment.as_slice());

            Ok(())
        }
        None => todo!("error handling"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;
    use std::env::current_dir;
    use std::process::Command;
    use std::string::String;

    // TODO: write a unit test without dependency on selfie and external files
    #[test]
    #[serial]
    fn can_disassemble_risc_u_binary() {
        let cd = String::from(current_dir().unwrap().to_str().unwrap());

        // generate RISC-U binary with Selfie
        let _ = Command::new("docker")
            .arg("run")
            .arg("-v")
            .arg(cd + ":/opt/monster")
            .arg("cksystemsteaching/selfie")
            .arg("/opt/selfie/selfie")
            .arg("-c")
            .arg("/opt/monster/symbolic/division-by-zero-3-35.c")
            .arg("-o")
            .arg("/opt/monster/symbolic/division-by-zero-3-35.riscu.o")
            .output();

        let test_file = Path::new("symbolic/division-by-zero-3-35.riscu.o");

        let result = disassemble_riscu(test_file);

        // TODO: test more than just this result
        assert!(result.is_ok());

        let _ = std::fs::remove_file(test_file);
    }
}

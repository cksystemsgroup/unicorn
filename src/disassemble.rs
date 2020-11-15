//! # Disassemble risc-v instructions

use crate::decode::{Decoder, RiscU};
use crate::elf::load_file;
use byteorder::{ByteOrder, LittleEndian};
use log::info;
use riscv_decode::{
    types::{BType, IType, JType, RType, SType, UType},
    Register,
};
use std::path::Path;

struct Disassembler {}

impl RiscU for Disassembler {
    fn lui(&mut self, i: UType) {
        info!("lui {:?},{:#x}", i.rd(), i.imm())
    }

    fn addi(&mut self, i: IType) {
        if i.rd() == Register::Zero && i.rs1() == Register::Zero && i.imm() == 0 {
            info!("nop")
        } else {
            info!("addi {:?},{:?},{}", i.rd(), i.rs1(), i.imm())
        }
    }

    fn add(&mut self, i: RType) {
        info!("add {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn sub(&mut self, i: RType) {
        info!("sub {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn mul(&mut self, i: RType) {
        info!("mul {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn divu(&mut self, i: RType) {
        info!("divu {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn remu(&mut self, i: RType) {
        info!("remu {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn sltu(&mut self, i: RType) {
        info!("sltu {:?},{:?},{:?}", i.rd(), i.rs1(), i.rs2())
    }

    fn ld(&mut self, i: IType) {
        info!("ld {:?},{}({:?})", i.rd(), i.imm(), i.rs1())
    }

    fn sd(&mut self, i: SType) {
        info!("sd {:?},{}({:?})", i.rs2(), i.imm(), i.rs1())
    }

    fn jal(&mut self, i: JType) {
        info!("jal {:?},{}", i.rd(), i.imm())
    }

    fn jalr(&mut self, i: IType) {
        info!("jalr {:?},{}({:?})", i.rd(), i.imm(), i.rs1())
    }

    fn beq(&mut self, i: BType) {
        info!("beq {:?},{:?},{}", i.rs1(), i.rs2(), i.imm())
    }

    fn ecall(&mut self) {
        info!("ecall")
    }
}

fn disassemble(binary: &[u8]) {
    let mut disassembler = Disassembler {};
    let mut pipeline = Decoder::new(&mut disassembler);

    binary
        .chunks_exact(4)
        .map(LittleEndian::read_u32)
        .for_each(|x| pipeline.run(x));
}

pub fn disassemble_riscu<P>(file: P) -> Result<(), String>
where
    P: AsRef<Path>,
{
    match load_file(file, 1024) {
        Some(program) => {
            disassemble(program.code_segment.as_slice());

            Ok(())
        }
        None => todo!("error handling"),
    }
}

use crate::elf::load_file;
use byteorder::{ByteOrder, LittleEndian};
use riscv_decode::types::*;
use std::path::Path;

use crate::decode::{Decoder, RiscU};

fn reg_to_str(reg: u32) -> String {
    match reg {
        0 => String::from("zero"),
        1 => String::from("ra"),
        2 => String::from("sp"),
        3 => String::from("gp"),
        4 => String::from("tp"),
        i if i >= 5 && i <= 7 => format!("t{}", i - 5),
        i if i >= 8 && i <= 9 => format!("s{}", i - 8),
        i if i >= 10 && i <= 17 => format!("a{}", i - 10),
        i if i >= 18 && i <= 27 => format!("s{}", i - 16),
        i if i >= 28 && i <= 31 => format!("t{}", i - 25),
        _ => unreachable!(),
    }
}

struct Disassembler {}

impl RiscU for Disassembler {
    fn lui(&mut self, i: UType) {
        println!("lui {},{:#x}", reg_to_str(i.rd()), i.imm())
    }

    // TODO: fix representation of negativ immediate values
    fn addi(&mut self, i: IType) {
        if i.rd() == 0 && i.rs1() == 0 && i.imm() == 0 {
            println!("nop")
        } else {
            println!(
                "addi {},{},{}",
                reg_to_str(i.rd()),
                reg_to_str(i.rs1()),
                i.imm()
            )
        }
    }

    fn add(&mut self, i: RType) {
        println!(
            "add {},{},{}",
            reg_to_str(i.rd()),
            reg_to_str(i.rs1()),
            reg_to_str(i.rs2())
        )
    }

    fn sub(&mut self, i: RType) {
        println!(
            "sub {},{},{}",
            reg_to_str(i.rd()),
            reg_to_str(i.rs1()),
            reg_to_str(i.rs2())
        )
    }

    fn mul(&mut self, i: RType) {
        println!(
            "mul {},{},{}",
            reg_to_str(i.rd()),
            reg_to_str(i.rs1()),
            reg_to_str(i.rs2())
        )
    }

    fn divu(&mut self, i: RType) {
        println!(
            "divu {},{},{}",
            reg_to_str(i.rd()),
            reg_to_str(i.rs1()),
            reg_to_str(i.rs2())
        )
    }

    fn remu(&mut self, i: RType) {
        println!(
            "remu {},{},{}",
            reg_to_str(i.rd()),
            reg_to_str(i.rs1()),
            reg_to_str(i.rs2())
        )
    }

    fn sltu(&mut self, i: RType) {
        println!(
            "sltu {},{},{}",
            reg_to_str(i.rd()),
            reg_to_str(i.rs1()),
            reg_to_str(i.rs2())
        )
    }

    fn ld(&mut self, i: IType) {
        println!(
            "ld {},{}({})",
            reg_to_str(i.rd()),
            i.imm(),
            reg_to_str(i.rs1())
        )
    }

    fn sd(&mut self, i: SType) {
        println!(
            "sd {},{}({})",
            reg_to_str(i.rs2()),
            i.imm(),
            reg_to_str(i.rs1())
        )
    }

    fn jal(&mut self, i: JType) {
        println!("jal {},{}", reg_to_str(i.rd()), i.imm())
    }

    fn jalr(&mut self, i: IType) {
        println!(
            "jalr {},{}({})",
            reg_to_str(i.rd()),
            i.imm(),
            reg_to_str(i.rs1())
        )
    }

    fn beq(&mut self, i: BType) {
        println!(
            "beq {},{},{}",
            reg_to_str(i.rs1()),
            reg_to_str(i.rs2()),
            i.imm()
        )
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
    match unsafe { load_file(file, 1024) } {
        Some((memory_vec, meta_data)) => {
            let memory = memory_vec.as_slice();

            disassemble(memory.split_at(meta_data.code_length as usize).0);

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

        std::fs::remove_file(test_file);
    }
}

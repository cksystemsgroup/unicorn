//! # Disassemble RISC-U instructions

use anyhow::Result;
use log::info;
use riscu::{
    load_object_file,
    types::{BType, IType, JType, RType, SType, UType},
    DecodedProgram, Instruction, Program, RiscuError,
};
use std::{fmt, mem::size_of, path::Path};

pub fn disassemble<P>(file: P) -> Result<()>
where
    P: AsRef<Path>,
{
    let program = time_info!(format!("loading {}", file.as_ref().display()).as_str(), {
        load_object_file(&file)?
    });

    time_info!(format!("decoding {}", file.as_ref().display()).as_str(), {
        let disassembly = Disassembly::from(&program)?;

        info!("dissasembly:\n{}", disassembly);
    });

    Ok(())
}

#[derive(Clone, Debug)]
pub struct Disassembly {
    decoded: DecodedProgram,
}

impl Disassembly {
    pub fn new(program: DecodedProgram) -> Self {
        Self { decoded: program }
    }

    pub fn from(program: &Program) -> Result<Self, RiscuError> {
        Ok(Self {
            decoded: program.decode()?,
        })
    }
}

impl From<Disassembly> for DecodedProgram {
    fn from(disassembly: Disassembly) -> DecodedProgram {
        disassembly.decoded
    }
}

impl<'a> fmt::Display for Disassembly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enumarte_with(
            self.decoded.code.content.as_slice().iter(),
            self.decoded.code.address,
            size_of::<u32>() as u64,
        )
        .try_for_each(|(pc, i)| print_instruction(f, pc, *i))
        .and_then(|_| {
            enumarte_with(
                self.decoded.data.content.as_slice().iter(),
                self.decoded.data.address,
                size_of::<u64>() as u64,
            )
            .try_for_each(|(pc, d)| writeln!(f, "{:#x}: .8byte {:#x}", pc, d))
        })
    }
}

fn enumarte_with<T>(
    iter: impl Iterator<Item = T>,
    start: u64,
    distance: u64,
) -> impl Iterator<Item = (u64, T)> {
    iter.enumerate()
        .map(move |(idx, t)| (start + (idx as u64) * distance, t))
}

fn print_instruction(f: &mut fmt::Formatter<'_>, pc: u64, i: Instruction) -> fmt::Result {
    match i {
        Instruction::Add(t) => print_rtype(f, pc, "add", t),
        Instruction::Addi(t) => print_itype(f, pc, "addi", t),
        Instruction::Sub(t) => print_rtype(f, pc, "sub", t),
        Instruction::Mul(t) => print_rtype(f, pc, "mul", t),
        Instruction::Divu(t) => print_rtype(f, pc, "divu", t),
        Instruction::Remu(t) => print_rtype(f, pc, "remu", t),
        Instruction::Sltu(t) => print_rtype(f, pc, "sltu", t),
        Instruction::Sd(t) => print_stype(f, pc, "sd", t),
        Instruction::Ld(t) => print_itype(f, pc, "ld", t),
        Instruction::Ecall(_) => writeln!(f, "{:#x}: ecall", pc),
        Instruction::Jal(t) => print_jtype(f, pc, "jal", t),
        Instruction::Jalr(t) => print_itype(f, pc, "jalr", t),
        Instruction::Beq(t) => print_btype(f, pc, "beq", t),
        Instruction::Lui(t) => print_utype(f, pc, "lui", t),
    }
}

fn print_rtype(f: &mut fmt::Formatter<'_>, pc: u64, op: &str, rtype: RType) -> fmt::Result {
    writeln!(
        f,
        "{:#x}: {} {:?},{:?},{:?}",
        pc,
        op,
        rtype.rd(),
        rtype.rs1(),
        rtype.rs2()
    )
}

fn print_itype(f: &mut fmt::Formatter<'_>, pc: u64, op: &str, itype: IType) -> fmt::Result {
    writeln!(
        f,
        "{:#x}: {} {:?},{:?},{}",
        pc,
        op,
        itype.rd(),
        itype.rs1(),
        itype.imm()
    )
}

fn print_stype(f: &mut fmt::Formatter<'_>, pc: u64, op: &str, stype: SType) -> fmt::Result {
    writeln!(
        f,
        "{:#x}: {} {:?},{}({:?})",
        pc,
        op,
        stype.rs2(),
        stype.imm(),
        stype.rs1()
    )
}

fn print_jtype(f: &mut fmt::Formatter<'_>, pc: u64, op: &str, jtype: JType) -> fmt::Result {
    writeln!(f, "{:#x}: {} {:?},{}", pc, op, jtype.rd(), jtype.imm())
}

fn print_btype(f: &mut fmt::Formatter<'_>, pc: u64, op: &str, btype: BType) -> fmt::Result {
    writeln!(
        f,
        "{:#x}: {} {:?},{:?},{}",
        pc,
        op,
        btype.rs1(),
        btype.rs2(),
        btype.imm()
    )
}

fn print_utype(f: &mut fmt::Formatter<'_>, pc: u64, op: &str, utype: UType) -> fmt::Result {
    writeln!(f, "{:#x}: {} {:?},{:#x}", pc, op, utype.rd(), utype.imm())
}

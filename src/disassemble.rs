//! # Disassemble RISC-V instructions

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

impl fmt::Display for Disassembly {
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
        Instruction::Lui(t) => print_utype(f, pc, "lui", t),
        Instruction::Auipc(t) => print_utype(f, pc, "auipc", t),
        Instruction::Jal(t) => print_jtype(f, pc, "jal", t),
        Instruction::Jalr(t) => print_itype(f, pc, "jalr", t),
        Instruction::Beq(t) => print_btype(f, pc, "beq", t),
        Instruction::Bne(t) => print_btype(f, pc, "bne", t),
        Instruction::Blt(t) => print_btype(f, pc, "blt", t),
        Instruction::Bge(t) => print_btype(f, pc, "bge", t),
        Instruction::Bltu(t) => print_btype(f, pc, "bltu", t),
        Instruction::Bgeu(t) => print_btype(f, pc, "bgeu", t),
        Instruction::Lb(t) => print_itype(f, pc, "lb", t),
        Instruction::Lh(t) => print_itype(f, pc, "lh", t),
        Instruction::Lw(t) => print_itype(f, pc, "lw", t),
        Instruction::Ld(t) => print_itype(f, pc, "ld", t),
        Instruction::Lbu(t) => print_itype(f, pc, "lbu", t),
        Instruction::Lhu(t) => print_itype(f, pc, "lhu", t),
        Instruction::Lwu(t) => print_itype(f, pc, "lwu", t),
        Instruction::Sb(t) => print_stype(f, pc, "sb", t),
        Instruction::Sh(t) => print_stype(f, pc, "sh", t),
        Instruction::Sw(t) => print_stype(f, pc, "sw", t),
        Instruction::Sd(t) => print_stype(f, pc, "sd", t),
        Instruction::Fence(t) => print_itype(f, pc, "fence", t),
        Instruction::Addi(t) => print_itype(f, pc, "addi", t),
        Instruction::Slti(t) => print_itype(f, pc, "slti", t),
        Instruction::Sltiu(t) => print_itype(f, pc, "sltiu", t),
        Instruction::Xori(t) => print_itype(f, pc, "xori", t),
        Instruction::Ori(t) => print_itype(f, pc, "ori", t),
        Instruction::Andi(t) => print_itype(f, pc, "andi", t),
        Instruction::Slli(t) => print_shift(f, pc, "slli", t),
        Instruction::Srli(t) => print_shift(f, pc, "srli", t),
        Instruction::Srai(t) => print_shift(f, pc, "srai", t),
        Instruction::Addiw(t) => print_itype(f, pc, "addiw", t),
        Instruction::Slliw(t) => print_shift(f, pc, "slliw", t),
        Instruction::Srliw(t) => print_shift(f, pc, "srliw", t),
        Instruction::Sraiw(t) => print_shift(f, pc, "sraiw", t),
        Instruction::Add(t) => print_rtype(f, pc, "add", t),
        Instruction::Sub(t) => print_rtype(f, pc, "sub", t),
        Instruction::Sll(t) => print_rtype(f, pc, "sll", t),
        Instruction::Slt(t) => print_rtype(f, pc, "slt", t),
        Instruction::Sltu(t) => print_rtype(f, pc, "sltu", t),
        Instruction::Xor(t) => print_rtype(f, pc, "xor", t),
        Instruction::Srl(t) => print_rtype(f, pc, "srl", t),
        Instruction::Sra(t) => print_rtype(f, pc, "sra", t),
        Instruction::Or(t) => print_rtype(f, pc, "or", t),
        Instruction::And(t) => print_rtype(f, pc, "and", t),
        Instruction::Mul(t) => print_rtype(f, pc, "mul", t),
        Instruction::Mulh(t) => print_rtype(f, pc, "mulh", t),
        Instruction::Mulhsu(t) => print_rtype(f, pc, "mulhsu", t),
        Instruction::Mulhu(t) => print_rtype(f, pc, "mulhu", t),
        Instruction::Div(t) => print_rtype(f, pc, "div", t),
        Instruction::Divu(t) => print_rtype(f, pc, "divu", t),
        Instruction::Rem(t) => print_rtype(f, pc, "rem", t),
        Instruction::Remu(t) => print_rtype(f, pc, "remu", t),
        Instruction::Addw(t) => print_rtype(f, pc, "addw", t),
        Instruction::Subw(t) => print_rtype(f, pc, "subw", t),
        Instruction::Sllw(t) => print_rtype(f, pc, "sllw", t),
        Instruction::Srlw(t) => print_rtype(f, pc, "srlw", t),
        Instruction::Sraw(t) => print_rtype(f, pc, "sraw", t),
        Instruction::Mulw(t) => print_rtype(f, pc, "mulw", t),
        Instruction::Divw(t) => print_rtype(f, pc, "divw", t),
        Instruction::Divuw(t) => print_rtype(f, pc, "divuw", t),
        Instruction::Remw(t) => print_rtype(f, pc, "remw", t),
        Instruction::Remuw(t) => print_rtype(f, pc, "remuw", t),
        Instruction::Ecall(_) => writeln!(f, "{:#x}: ecall", pc),
        _ => todo!("{:?}", i),
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

fn print_shift(f: &mut fmt::Formatter<'_>, pc: u64, op: &str, itype: IType) -> fmt::Result {
    writeln!(
        f,
        "{:#x}: {} {:?},{:?},{}",
        pc,
        op,
        itype.rd(),
        itype.rs1(),
        itype.imm() & 0x3f
    )
}

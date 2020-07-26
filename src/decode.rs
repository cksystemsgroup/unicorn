use riscv_decode::{Instruction, decode};

pub trait RiscU: Sized + 'static {
    fn lui(&mut self, imm: u32, rd: u32);
    fn addi(&mut self, rd: u32, rs1: u32, imm: u32);
    fn add(&mut self, rd: u32, rs1: u32, rs2: u32);
    fn sub(&mut self, rd: u32, rs1: u32, rs2: u32);
    fn mul(&mut self, rd: u32, rs1: u32, rs2: u32);
    fn divu(&mut self, rd: u32, rs1: u32, rs2: u32);
    fn remu(&mut self, rd: u32, rs1: u32, rs2: u32);
    fn sltu(&mut self, rd: u32, rs1: u32, rs2: u32);
    fn ld(&mut self, rd: u32, imm: u32, rs1: u32);
    fn sd(&mut self, rs2: u32, imm: u32, rs1: u32);
    fn jal(&mut self, rd: u32, imm: u32);
    fn jalr(&mut self, rd: u32, imm: u32, rs1: u32);
    fn beq(&mut self, rs1: u32, rs2: u32, imm: u32);
    fn ecall(&mut self);
}

pub struct Decoder<'a, RiscU> {
    next: &'a mut RiscU,
}
impl<R: RiscU> Decoder<'_, R> {
    pub fn new(next: &mut R) -> Decoder<R> {
        Decoder {
            next,
        }
    }
}
impl<R: RiscU> Decoder<'_, R> {
    pub fn run(&mut self, instruction: u32) {
        match decode(instruction) {
            Ok(instr) => match instr {
                Instruction::Lui(i) => self.next.lui(i.imm(), i.rd()),
                Instruction::Addi(i) => self.next.addi(i.rd(), i.rs1(), i.imm()),
                Instruction::Add(i) => self.next.add(i.rd(), i.rs1(), i.rs2()),
                Instruction::Sub(i) => self.next.sub(i.rd(), i.rs1(), i.rs2()),
                Instruction::Mul(i) => self.next.mul(i.rd(), i.rs1(), i.rs2()),
                Instruction::Divu(i) => self.next.divu(i.rd(), i.rs1(), i.rs2()),
                Instruction::Remu(i) => self.next.remu(i.rd(), i.rs1(), i.rs2()),
                Instruction::Sltu(i) => self.next.sltu(i.rd(), i.rs1(), i.rs2()),
                Instruction::Ld(i) => self.next.ld(i.rd(), i.imm(), i.rs1()),
                Instruction::Sd(i) => self.next.sd(i.rs2(), i.imm(), i.rs1()),
                Instruction::Jal(i) => self.next.jal(i.rd(), i.imm()),
                Instruction::Jalr(i) => self.next.jalr(i.rd(), i.imm(), i.rs1()),
                Instruction::Beq(i) => self.next.beq(i.rs1(), i.rs2(), i.imm()),
                Instruction::Ecall => self.next.ecall(),
                _ => unimplemented!(),
            }
            _ => unimplemented!()
        }
    }
}
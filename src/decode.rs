use riscv_decode::types::*;
use riscv_decode::{decode, Instruction};

pub trait RiscU: Sized + 'static {
    fn lui(&mut self, i: UType);
    fn addi(&mut self, i: IType);
    fn add(&mut self, i: RType);
    fn sub(&mut self, i: RType);
    fn mul(&mut self, i: RType);
    fn divu(&mut self, i: RType);
    fn remu(&mut self, i: RType);
    fn sltu(&mut self, i: RType);
    fn ld(&mut self, i: IType);
    fn sd(&mut self, i: SType);

    fn jal(&mut self, i: JType);
    fn jalr(&mut self, i: IType);
    fn beq(&mut self, i: BType);
    fn ecall(&mut self);
}

pub struct Decoder<'a, RiscU> {
    pub next: &'a mut RiscU,
}
impl<R: RiscU> Decoder<'_, R> {
    pub fn new(next: &mut R) -> Decoder<R> {
        Decoder { next }
    }
}
impl<R: RiscU> Decoder<'_, R> {
    pub fn run(&mut self, instruction: u32) {
        match decode(instruction) {
            Ok(instr) => match instr {
                Instruction::Lui(i) => self.next.lui(i),
                Instruction::Addi(i) => self.next.addi(i),
                Instruction::Add(i) => self.next.add(i),
                Instruction::Sub(i) => self.next.sub(i),
                Instruction::Mul(i) => self.next.mul(i),
                Instruction::Divu(i) => self.next.divu(i),
                Instruction::Remu(i) => self.next.remu(i),
                Instruction::Sltu(i) => self.next.sltu(i),
                Instruction::Ld(i) => self.next.ld(i),
                Instruction::Sd(i) => self.next.sd(i),
                Instruction::Jal(i) => self.next.jal(i),
                Instruction::Jalr(i) => self.next.jalr(i),
                Instruction::Beq(i) => self.next.beq(i),
                Instruction::Ecall => self.next.ecall(),
                _ => unimplemented!(),
            },
            _ => unimplemented!(),
        }
    }
}

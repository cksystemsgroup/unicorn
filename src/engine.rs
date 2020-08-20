use crate::ternary::TernaryBitVector;

struct Machine {
    #[allow(dead_code)]
    regs: [TernaryBitVector; 32],
}

impl Machine {
    #[allow(dead_code)]
    fn new() -> Self {
        Machine {
            regs: [TernaryBitVector::new(0, u64::max_value()); 32],
        }
    }
}

// fn has_inv_value_for_addi(raw: IType) -> bool {
//     true
// }

#[cfg(test)]
mod tests {
    use super::*;
    use riscv_decode::types::*;
    use riscv_decode::Instruction;

    #[test]
    fn can_find_input_for_addi() {
        let machine = Machine::new();

        let raw = IType(0);
        let _addi = Instruction::Addi(raw);

        let _rd = raw.rd();
        let _rs1_value = machine.regs[raw.rs1() as usize];

        let _s = raw.imm();
    }
}

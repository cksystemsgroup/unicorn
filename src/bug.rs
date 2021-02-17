use crate::{
    engine::{instruction_to_str, Value},
    solver::BitVector,
    symbolic_state::BVOperator,
};
use riscu::Instruction;
use std::fmt;

#[derive(Debug, Clone)]
pub enum Bug {
    DivisionByZero {
        info: BasicInfo,
    },

    AccessToUnitializedMemory {
        info: BasicInfo,
        instruction: Instruction,
        operands: Vec<Value>,
    },

    AccessToUnalignedAddress {
        info: BasicInfo,
        address: u64,
    },

    AccessToOutOfRangeAddress {
        info: BasicInfo,
    },

    ExitCodeGreaterZero {
        info: BasicInfo,
    },
}

impl fmt::Display for Bug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Bug::DivisionByZero { info } => write!(f, "reason: division by zero\n{}", info),
            Bug::AccessToUnitializedMemory {
                info,
                instruction,
                operands,
            } => write!(
                f,
                "reason: access to uninitialized memory\ninstruction: {}\noperands {:?}\n{}",
                instruction_to_str(*instruction),
                operands,
                info,
            ),
            Bug::AccessToUnalignedAddress { info, address } => write!(
                f,
                "reason: access to unaligned memory address {:#x}\n{}",
                address, info
            ),
            Bug::AccessToOutOfRangeAddress { info } => write!(
                f,
                "reason: accessed a memory address out of virtual address space\n{}",
                info,
            ),
            Bug::ExitCodeGreaterZero { info } => write!(f, "exit code greater than zero\n{}", info),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BasicInfo {
    pub witness: Witness,
    pub pc: u64,
}

impl fmt::Display for BasicInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "pc: {:#010x}\nwitness: {}", self.pc, self.witness)
    }
}

#[derive(Debug, Clone)]
pub enum Term {
    Constant(u64),
    Variable(String, u64),
    Unary(BVOperator, usize, u64),
    Binary(usize, BVOperator, usize, u64),
}

#[derive(Debug, Clone)]
pub struct Witness {
    assignments: Vec<Term>,
}

impl Default for Witness {
    fn default() -> Self {
        Self {
            assignments: Vec::new(),
        }
    }
}

impl Witness {
    pub fn new() -> Self {
        Witness::default()
    }

    pub fn add_constant(&mut self, value: BitVector) -> usize {
        self.assignments.push(Term::Constant(value.0));

        self.assignments.len() - 1
    }

    pub fn add_variable(&mut self, name: &str, result: BitVector) -> usize {
        self.assignments
            .push(Term::Variable(name.to_owned(), result.0));

        self.assignments.len() - 1
    }

    pub fn add_unary(&mut self, op: BVOperator, v: usize, result: BitVector) -> usize {
        self.assignments.push(Term::Unary(op, v, result.0));

        self.assignments.len() - 1
    }

    pub fn add_binary(
        &mut self,
        lhs: usize,
        op: BVOperator,
        rhs: usize,
        result: BitVector,
    ) -> usize {
        self.assignments.push(Term::Binary(lhs, op, rhs, result.0));

        self.assignments.len() - 1
    }
}

impl fmt::Display for Witness {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "[").and_then(|_| {
            self.assignments
                .clone()
                .into_iter()
                .enumerate()
                .try_for_each(|(id, a)| match a {
                    Term::Constant(c) => writeln!(f, "  x{} := {},", id, c),
                    Term::Variable(name, v) => writeln!(f, "  x{} := {:?} ({}),", id, name, v),
                    Term::Unary(op, x, v) => writeln!(f, "  x{} := {}x{} ({}),", id, op, x, v),
                    Term::Binary(lhs, op, rhs, v) => {
                        writeln!(f, "  x{} := x{} {} x{} ({}),", id, lhs, op, rhs, v)
                    }
                })
                .and_then(|_| writeln!(f, "]"))
        })
    }
}

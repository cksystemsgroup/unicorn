use super::system::instruction_to_str;
use riscu::Instruction;
use std::fmt;

pub trait BugInfo: fmt::Display + fmt::Debug + Clone {
    type Value: fmt::Display + fmt::Debug + Clone;
}

#[derive(Debug, Clone)]
pub enum Bug<Info: BugInfo> {
    DivisionByZero {
        info: Info,
    },

    AccessToUnitializedMemory {
        info: Info,
        reason: UninitializedMemoryAccessReason<Info>,
    },

    AccessToUnalignedAddress {
        info: Info,
        address: u64,
    },

    AccessToOutOfRangeAddress {
        info: Info,
    },

    ExitCodeGreaterZero {
        info: Info,
        exit_code: Info::Value,
        address: u64,
    },
}

impl<Info> fmt::Display for Bug<Info>
where
    Info: BugInfo,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Bug::DivisionByZero { info } => write!(f, "reason: division by zero\n{}", info),
            Bug::AccessToUnitializedMemory { info, reason } => write!(
                f,
                "reason: access to uninitialized memory\n{}\n{}",
                info, reason,
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
            Bug::ExitCodeGreaterZero {
                info,
                exit_code,
                address,
            } => write!(
                f,
                "reason: exit code ({}) greater than zero at pc={:#x}\n{}",
                exit_code, address, info
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub enum UninitializedMemoryAccessReason<Info: BugInfo> {
    ReadUnintializedMemoryAddress {
        description: String,
        address: u64,
    },
    InstructionWithUninitializedOperand {
        instruction: Instruction,
        operands: Vec<Info::Value>,
    },
}

impl<Info> fmt::Display for UninitializedMemoryAccessReason<Info>
where
    Info: BugInfo,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UninitializedMemoryAccessReason::InstructionWithUninitializedOperand {
                instruction,
                operands,
            } => write!(
                f,
                "instruction: {}  operands: {:?}",
                instruction_to_str(*instruction),
                operands
            ),
            UninitializedMemoryAccessReason::ReadUnintializedMemoryAddress {
                description,
                address,
            } => write!(f, "{} (pc: {:#x})", description, address),
        }
    }
}

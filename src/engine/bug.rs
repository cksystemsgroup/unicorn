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
        instruction: Instruction,
        operands: Vec<Info::Value>,
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
    },
}

impl<Info> fmt::Display for Bug<Info>
where
    Info: BugInfo,
{
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

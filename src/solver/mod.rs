mod bitvec;
mod external;
mod monster;

#[cfg(feature = "boolector-solver")]
mod boolector;

#[cfg(feature = "z3-solver")]
mod z3;

#[cfg(feature = "boolector-solver")]
pub use self::boolector::*;

#[cfg(feature = "z3-solver")]
pub use self::z3::*;

pub use self::{bitvec::*, external::*, monster::*};

use crate::symbolic_state::{Formula, SymbolId};
use log::debug;
use std::{collections::HashMap, convert::From, io};
use thiserror::Error;

pub type Assignment<T> = HashMap<SymbolId, T>;

pub trait Solver: Default {
    fn name() -> &'static str;

    fn solve(
        &self,
        formula: &Formula,
        root: SymbolId,
    ) -> Result<Option<Assignment<BitVector>>, SolverError> {
        debug!("try to solve with {} solver", Self::name());

        time_debug!("finished solving formula", {
            self.solve_impl(formula, root)
        })
    }

    fn solve_impl(
        &self,
        formula: &Formula,
        root: SymbolId,
    ) -> Result<Option<Assignment<BitVector>>, SolverError>;
}

#[derive(Debug, Error, Clone)]
pub enum SolverError {
    #[error("failed to compute satisfiability within the given limits")]
    SatUnknown,

    #[error("could not find a satisfiable assignment before timing out")]
    Timeout,

    #[error("solver failed with IO error")]
    IoError(String),
}

impl From<io::Error> for SolverError {
    fn from(err: io::Error) -> Self {
        SolverError::IoError(err.to_string())
    }
}

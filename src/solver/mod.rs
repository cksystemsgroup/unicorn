pub mod boolector;
pub mod external;
pub mod monster;
pub mod z3;

pub use self::{boolector::*, external::*, monster::*, z3::*};

use crate::{
    bitvec::*,
    symbolic_state::{Formula, SymbolId},
};
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

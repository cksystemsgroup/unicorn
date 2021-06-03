mod bitvec;
mod monster;
mod smt;

#[cfg(feature = "boolector")]
mod boolector;

#[cfg(feature = "z3")]
mod z3;

#[cfg(feature = "boolector")]
pub use self::boolector::*;

#[cfg(feature = "z3")]
pub use self::z3::*;

pub use self::{bitvec::*, monster::*, smt::*};

use log::debug;
use std::marker::Sync;
use std::{collections::HashMap, convert::From, fmt, io, ops::Index};
use strum::{EnumString, EnumVariantNames, IntoStaticStr};
use thiserror::Error;

pub type Assignment = HashMap<SymbolId, BitVector>;

pub trait Solver: Default + Sync + Sized {
    fn name() -> &'static str;

    fn solve<F: Formula>(&self, formula: &F) -> Result<Option<Assignment>, SolverError> {
        debug!("try to solve with {} backend", Self::name());

        time_debug!("finished solving formula", { self.solve_impl(formula) })
    }

    fn solve_impl<F: Formula>(&self, formula: &F) -> Result<Option<Assignment>, SolverError>;
}

pub trait SmtSolver: Solver {
    fn smt_options() -> &'static str;
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

#[derive(Debug, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum SolverType {
    Monster,
    #[cfg(feature = "boolector")]
    Boolector,
    #[cfg(feature = "z3")]
    Z3,
}

impl From<io::Error> for SolverError {
    fn from(err: io::Error) -> Self {
        SolverError::IoError(err.to_string())
    }
}

#[derive(Clone, Debug, Copy, Eq, Hash, PartialEq)]
pub enum OperandSide {
    Lhs,
    Rhs,
}

impl OperandSide {
    #[allow(dead_code)]
    pub fn other(&self) -> Self {
        match self {
            OperandSide::Lhs => OperandSide::Rhs,
            OperandSide::Rhs => OperandSide::Lhs,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum BVOperator {
    Add,
    Sub,
    Mul,
    Divu,
    Sltu,
    Remu,
    Not,
    Equals,
    BitwiseAnd,
}

impl BVOperator {
    pub fn is_unary(&self) -> bool {
        *self == BVOperator::Not
    }
    pub fn is_binary(&self) -> bool {
        !self.is_unary()
    }
}

impl fmt::Display for BVOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BVOperator::Add => "+",
                BVOperator::Sub => "-",
                BVOperator::Mul => "*",
                BVOperator::Divu => "/",
                BVOperator::Not => "!",
                BVOperator::Remu => "%",
                BVOperator::Equals => "=",
                BVOperator::BitwiseAnd => "&",
                BVOperator::Sltu => "<",
            }
        )
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Symbol {
    Constant(BitVector),
    Input(String),
    Operator(BVOperator),
}

pub type SymbolId = usize;

pub trait Formula: Index<SymbolId, Output = Symbol> {
    type DependencyIter: Iterator<Item = SymbolId>;
    type SymbolIdsIter: Iterator<Item = SymbolId>;

    fn root(&self) -> SymbolId;

    fn operands(&self, sym: SymbolId) -> (SymbolId, Option<SymbolId>);

    fn operand(&self, sym: SymbolId) -> SymbolId;

    fn dependencies(&self, sym: SymbolId) -> Self::DependencyIter;
    //where
    //Iter: Iterator<Item = SymbolId>;

    fn symbol_ids(&self) -> Self::SymbolIdsIter;
    //where
    //Iter: Iterator<Item = SymbolId>;

    fn is_operand(&self, sym: SymbolId) -> bool;

    fn traverse<V, R>(&self, n: SymbolId, visit_map: &mut HashMap<SymbolId, R>, v: &mut V) -> R
    where
        V: FormulaVisitor<R>,
        R: Clone;
}

pub trait FormulaVisitor<T>: Sized {
    fn input(&mut self, idx: SymbolId, name: &str) -> T;
    fn constant(&mut self, idx: SymbolId, v: BitVector) -> T;
    fn unary(&mut self, idx: SymbolId, op: BVOperator, v: T) -> T;
    fn binary(&mut self, idx: SymbolId, op: BVOperator, lhs: T, rhs: T) -> T;
}

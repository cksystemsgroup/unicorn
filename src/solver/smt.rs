use super::{
    Assignment, BVOperator, BitVector, Formula, FormulaVisitor, SmtSolver, Solver, SolverError,
    SymbolId,
};
use std::{
    collections::HashMap,
    io::{stdout, BufWriter, Write},
    sync::{Arc, Mutex},
};
use strum::{EnumString, EnumVariantNames, IntoStaticStr};

#[derive(Debug, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum SmtType {
    Generic,
    #[cfg(feature = "boolector")]
    Boolector,
    #[cfg(feature = "z3")]
    Z3,
}

pub struct SmtWriter {
    output: Arc<Mutex<dyn Write + Send>>,
}

const SET_LOGIC_STATEMENT: &str = "(set-logic QF_BV)";

impl SmtWriter {
    pub fn new<W: 'static>(write: W) -> Result<Self, SolverError>
    where
        W: Write + Send,
    {
        Self::new_with_smt_prefix(write, "")
    }

    pub fn new_for_solver<S, W: 'static>(write: W) -> Result<Self, SolverError>
    where
        S: SmtSolver,
        W: Write + Send,
    {
        Self::new_with_smt_prefix(write, S::smt_options())
    }

    fn new_with_smt_prefix<W: 'static>(write: W, prefix: &str) -> Result<Self, SolverError>
    where
        W: Write + Send,
    {
        let mut writer = BufWriter::new(write);

        writeln!(writer, "{}{}", prefix, SET_LOGIC_STATEMENT).map_err(SolverError::from)?;

        let output = Arc::new(Mutex::new(writer));

        Ok(Self { output })
    }
}

impl Default for SmtWriter {
    fn default() -> Self {
        Self::new_with_smt_prefix(stdout(), "").expect("stdout should not fail")
    }
}

impl Solver for SmtWriter {
    fn name() -> &'static str {
        "External"
    }

    fn solve_impl<F: Formula>(&self, formula: &F) -> Result<Option<Assignment>, SolverError> {
        {
            let mut output = self.output.lock().expect("no other thread should fail");

            writeln!(output, "(push 1)")?;

            // give lock back here
        }

        let mut printer = SmtPrinter {
            output: self.output.clone(),
        };
        let mut visited = HashMap::<SymbolId, Result<SymbolId, SolverError>>::new();

        formula.traverse(formula.root(), &mut visited, &mut printer)?;

        let mut output = self.output.lock().expect("no other thread should fail");

        writeln!(output, "(check-sat)\n(get-model)\n(pop 1)")?;

        output.flush().expect("can flush SMT write buffer");

        Err(SolverError::SatUnknown)
    }
}

struct SmtPrinter {
    output: Arc<Mutex<dyn Write>>,
}

impl FormulaVisitor<Result<SymbolId, SolverError>> for SmtPrinter {
    fn input(&mut self, idx: SymbolId, name: &str) -> Result<SymbolId, SolverError> {
        let mut o = self.output.lock().expect("no other thread should fail");

        writeln!(o, "(declare-fun x{} () (_ BitVec 64)); {:?}", idx, name)?;

        Ok(idx)
    }

    fn constant(&mut self, idx: SymbolId, v: BitVector) -> Result<SymbolId, SolverError> {
        let mut o = self.output.lock().expect("no other thread should fail");

        writeln!(
            o,
            "(declare-fun x{} () (_ BitVec 64))\n(assert (= x{} (_ bv{} 64)))",
            idx, idx, v.0
        )?;

        Ok(idx)
    }

    fn unary(
        &mut self,
        idx: SymbolId,
        op: BVOperator,
        v: Result<SymbolId, SolverError>,
    ) -> Result<SymbolId, SolverError> {
        let mut o = self.output.lock().expect("no other thread should fail");

        match op {
            BVOperator::Not => {
                writeln!(
                    o,
                    "(declare-fun x{} () (_ BitVec 64))\n(assert (= x{} (ite (= x{} (_ bv0 64)) (_ bv1 64) (_ bv0 64))))",
                    idx, idx, v?,
                )?;
            }
            _ => unreachable!("operator {} not supported as unary operator", op),
        }

        Ok(idx)
    }

    fn binary(
        &mut self,
        idx: SymbolId,
        op: BVOperator,
        lhs: Result<SymbolId, SolverError>,
        rhs: Result<SymbolId, SolverError>,
    ) -> Result<SymbolId, SolverError> {
        let mut o = self.output.lock().expect("no other thread should fail");

        match op {
            BVOperator::Equals | BVOperator::Sltu => {
                writeln!(
                    o,
                    "(declare-fun x{} () (_ BitVec 64))\n(assert (= x{} (ite ({} x{} x{}) (_ bv1 64) (_ bv0 64))))",
                    idx,
                    idx,
                    to_smt(op),
                    lhs?,
                    rhs?
                )?;
            }
            _ => {
                writeln!(
                    o,
                    "(declare-fun x{} () (_ BitVec 64))\n(assert (= x{} ({} x{} x{})))",
                    idx,
                    idx,
                    to_smt(op),
                    lhs?,
                    rhs?
                )?;
            }
        };

        Ok(idx)
    }
}

fn to_smt(op: BVOperator) -> &'static str {
    match op {
        BVOperator::Add => "bvadd",
        BVOperator::Sub => "bvsub",
        BVOperator::Not => panic!("no direct translation"),
        BVOperator::Mul => "bvmul",
        BVOperator::Divu => "bvudiv",
        BVOperator::Remu => "bvurem",
        BVOperator::Equals => "=",
        BVOperator::BitwiseAnd => "bvand",
        BVOperator::Sltu => "bvult",
    }
}

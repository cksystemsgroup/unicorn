use super::{
    Assignment, BVOperator, BitVector, Formula, Solver, SolverError,
    Symbol::{Constant, Input, Operator},
    SymbolId,
};
use boolector_solver::{
    option::{BtorOption, ModelGen, OutputFileFormat},
    Btor, SolverResult, BV,
};
use std::{collections::HashMap, rc::Rc};

pub struct Boolector {}

impl Boolector {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for Boolector {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver for Boolector {
    fn name() -> &'static str {
        "Boolector"
    }

    fn solve_impl<F: Formula>(&self, formula: &F) -> Result<Option<Assignment>, SolverError> {
        let solver = Rc::new(Btor::new());
        solver.set_opt(BtorOption::ModelGen(ModelGen::All));
        solver.set_opt(BtorOption::Incremental(true));
        solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));

        let mut bvs = HashMap::new();
        let bv = traverse(formula, formula.root(), &solver, &mut bvs);
        bv.slice(0, 0).assert();

        match solver.sat() {
            SolverResult::Sat => {
                let assignments = formula
                    .symbol_ids()
                    .filter_map(|i| {
                        bvs.get(&i).map(|bv| {
                            (
                                i,
                                BitVector(
                                    bv.get_a_solution()
                                        .as_u64()
                                        .expect("BV always fits in 64 bits for our machine"),
                                ),
                            )
                        })
                    })
                    .collect();

                Ok(Some(assignments))
            }
            SolverResult::Unsat => Ok(None),
            SolverResult::Unknown => Err(SolverError::SatUnknown),
        }
    }
}

fn traverse<'a, F: Formula>(
    formula: &F,
    sym: SymbolId,
    solver: &'a Rc<Btor>,
    bvs: &mut HashMap<SymbolId, BV<Rc<Btor>>>,
) -> BV<Rc<Btor>> {
    let bv =
        match &formula[sym] {
            Operator(op) => match formula.operands(sym) {
                (lhs, Some(rhs)) => match op {
                    BVOperator::Add => traverse(formula, lhs, solver, bvs)
                        .add(&traverse(formula, rhs, solver, bvs)),
                    BVOperator::Sub => traverse(formula, lhs, solver, bvs)
                        .sub(&traverse(formula, rhs, solver, bvs)),
                    BVOperator::Mul => traverse(formula, lhs, solver, bvs)
                        .mul(&traverse(formula, rhs, solver, bvs)),
                    BVOperator::Equals => traverse(formula, lhs, solver, bvs)
                        ._eq(&traverse(formula, rhs, solver, bvs))
                        .uext(63),
                    BVOperator::BitwiseAnd => traverse(formula, lhs, solver, bvs)
                        .and(&traverse(formula, rhs, solver, bvs)),
                    BVOperator::Divu => traverse(formula, lhs, solver, bvs)
                        .udiv(&traverse(formula, rhs, solver, bvs)),
                    BVOperator::Remu => traverse(formula, lhs, solver, bvs)
                        .urem(&traverse(formula, rhs, solver, bvs)),
                    BVOperator::Sltu => traverse(formula, lhs, solver, bvs)
                        .ult(&traverse(formula, rhs, solver, bvs))
                        .uext(63),
                    i => unreachable!("binary operator: {:?}", i),
                },
                (lhs, None) => match op {
                    BVOperator::Not => traverse(formula, lhs, solver, bvs)
                        ._eq(&BV::from_u64(solver.clone(), 0, 64))
                        .uext(63),
                    i => unreachable!("unary operator: {:?}", i),
                },
            },
            Input(name) => {
                if let Some(value) = bvs.get(&sym) {
                    value.clone()
                } else {
                    // input names are not unique in the formula, but symbol-ids are unique
                    BV::new(
                        solver.clone(),
                        64,
                        Some(format!("x{}: {}", sym, name).as_str()),
                    )
                }
            }
            Constant(c) => BV::from_u64(solver.clone(), (*c).0, 64),
        };

    bvs.insert(sym, bv.clone());
    bv
}

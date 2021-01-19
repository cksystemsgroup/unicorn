use crate::{
    bitvec::BitVector,
    solver::{Assignment, Solver, SolverError},
    symbolic_state::{
        get_operands, BVOperator, Formula,
        Node::{Constant, Input, Operator},
        SymbolId,
    },
};
use boolector::{
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

    fn solve_impl(
        &self,
        graph: &Formula,
        root: SymbolId,
    ) -> Result<Option<Assignment<BitVector>>, SolverError> {
        let solver = Rc::new(Btor::new());
        solver.set_opt(BtorOption::ModelGen(ModelGen::All));
        solver.set_opt(BtorOption::Incremental(true));
        solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));

        let mut bvs = HashMap::new();
        let bv = traverse(graph, root, &solver, &mut bvs);
        bv.slice(0, 0).assert();

        match solver.sat() {
            SolverResult::Sat => {
                let assignments = graph
                    .node_indices()
                    .map(|i| {
                        let bv = bvs.get(&i).expect("every input must be part of bvs");

                        BitVector(
                            bv.get_a_solution()
                                .as_u64()
                                .expect("BV always fits in 64 bits for our machine"),
                        )
                    })
                    .collect();

                Ok(Some(assignments))
            }
            SolverResult::Unsat => Ok(None),
            SolverResult::Unknown => Err(SolverError::SatUnknown),
        }
    }
}

fn traverse<'a>(
    graph: &Formula,
    node: SymbolId,
    solver: &'a Rc<Btor>,
    bvs: &mut HashMap<SymbolId, BV<Rc<Btor>>>,
) -> BV<Rc<Btor>> {
    let bv =
        match &graph[node] {
            Operator(op) => {
                match get_operands(graph, node) {
                    (lhs, Some(rhs)) => match op {
                        BVOperator::Add => traverse(graph, lhs, solver, bvs)
                            .add(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Sub => traverse(graph, lhs, solver, bvs)
                            .sub(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Mul => traverse(graph, lhs, solver, bvs)
                            .mul(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Equals => traverse(graph, lhs, solver, bvs)
                            ._eq(&traverse(graph, rhs, solver, bvs))
                            .uext(63),
                        BVOperator::BitwiseAnd => traverse(graph, lhs, solver, bvs)
                            .and(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Divu => traverse(graph, lhs, solver, bvs)
                            .udiv(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Remu => traverse(graph, lhs, solver, bvs)
                            .urem(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Sltu => traverse(graph, lhs, solver, bvs)
                            .ult(&traverse(graph, rhs, solver, bvs))
                            .uext(63),
                        i => unreachable!("binary operator: {:?}", i),
                    },
                    (lhs, None) => match op {
                        BVOperator::Not => traverse(graph, lhs, solver, bvs)
                            ._eq(&BV::from_u64(solver.clone(), 0, 64))
                            .uext(63),
                        i => unreachable!("unary operator: {:?}", i),
                    },
                }
            }
            Input(name) => {
                if let Some(value) = bvs.get(&node) {
                    value.clone()
                } else {
                    BV::new(solver.clone(), 64, Some(name))
                }
            }
            Constant(c) => BV::from_u64(solver.clone(), *c, 64),
        };

    bvs.insert(node, bv.clone());
    bv
}

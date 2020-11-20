use crate::bitvec::BitVector;
use crate::solver::{Assignment, Solver};
use crate::symbolic_state::{
    get_operands, BVOperator, Formula,
    Node::{Constant, Input, Operator},
    SymbolId,
};
use boolector::{
    option::{BtorOption, ModelGen, OutputFileFormat},
    Btor, SolverResult, BV,
};
use std::collections::HashMap;
use std::rc::Rc;

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

    fn solve_impl(&mut self, graph: &Formula, root: SymbolId) -> Option<Assignment<BitVector>> {
        let solver = Rc::new(Btor::new());
        solver.set_opt(BtorOption::ModelGen(ModelGen::All));
        solver.set_opt(BtorOption::Incremental(true));
        solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));

        let mut bvs = HashMap::new();
        let bv = traverse(graph, root, &solver, &mut bvs);
        bv.assert();

        if let SolverResult::Sat = solver.sat() {
            let assignments = graph
                .node_indices()
                .filter(|i| matches!(graph[*i], Input(_)))
                .map(|i| {
                    let bv = bvs.get(&i).expect("every input must be part of bvs");

                    BitVector(
                        bv.get_a_solution()
                            .as_u64()
                            .expect("BV always fits in 64 bits for our machine"),
                    )
                })
                .collect();

            Some(assignments)
        } else {
            None
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
            Operator(op) => match get_operands(graph, node) {
                (lhs, Some(rhs)) => {
                    match op {
                        BVOperator::Add => traverse(graph, lhs, solver, bvs)
                            .add(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Sub => traverse(graph, lhs, solver, bvs)
                            .sub(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Mul => traverse(graph, lhs, solver, bvs)
                            .mul(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Equals => traverse(graph, lhs, solver, bvs)
                            ._eq(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::BitwiseAnd => traverse(graph, lhs, solver, bvs)
                            .and(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Divu => traverse(graph, lhs, solver, bvs)
                            .udiv(&traverse(graph, rhs, solver, bvs)),
                        BVOperator::Sltu => traverse(graph, lhs, solver, bvs)
                            .slt(&traverse(graph, rhs, solver, bvs)),
                        i => unimplemented!("binary operator: {:?}", i),
                    }
                }
                (lhs, None) => match op {
                    BVOperator::Not => {
                        traverse(graph, lhs, solver, bvs)._eq(&BV::from_u64(solver.clone(), 0, 1))
                    }
                    i => unimplemented!("unary operator: {:?}", i),
                },
            },
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

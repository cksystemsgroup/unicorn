use crate::bitvec::BitVector;
use crate::solver::{Assignment, Solver};
use crate::symbolic_state::{
    ArgumentSide, BVOperator, Formula,
    Node::{Constant, Input, Operator},
};
use boolector::{
    option::{BtorOption, ModelGen, OutputFileFormat},
    Btor, SolverResult, BV,
};
use petgraph::{graph::NodeIndex, Direction};
use std::collections::HashMap;
use std::rc::Rc;

fn solve(graph: &Formula, root: NodeIndex) -> Option<Assignment<BitVector>> {
    let solver = Rc::new(Btor::new());
    solver.set_opt(BtorOption::ModelGen(ModelGen::All));
    solver.set_opt(BtorOption::Incremental(true));
    solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));

    let mut bvs = HashMap::new();
    let bv = traverse(graph, root, &solver, &mut bvs);
    bv.assert();

    let result = solver.sat();
    println!("result: {:?}\n", result);
    print!("constraints: \n{}\n", solver.print_constraints());
    print!("assignment: \n{}\n", solver.print_model());
    println!();

    if let SolverResult::Sat = result {
        let assignments = graph
            .node_indices()
            .map(|i| BitVector(bvs.get(&i).unwrap().get_a_solution().as_u64().unwrap()))
            .collect();

        Some(assignments)
    } else {
        None
    }
}

fn get_operands(
    graph: &Formula,
    node: NodeIndex,
    solver: &Rc<Btor>,
    bvs: &mut HashMap<NodeIndex, BV<Rc<Btor>>>,
) -> (BV<Rc<Btor>>, Option<BV<Rc<Btor>>>) {
    let mut operands = graph.neighbors_directed(node, Direction::Incoming).detach();

    match operands.next(graph) {
        Some(p) if graph[p.0] == ArgumentSide::Lhs => (traverse(graph, p.1, solver, bvs), {
            if let Some(node) = operands.next(graph) {
                Some(traverse(graph, node.1, solver, bvs))
            } else {
                None
            }
        }),
        Some(p) if graph[p.0] == ArgumentSide::Rhs => (
            traverse(graph, p.1, solver, bvs),
            if let Some(node) = operands.next(graph) {
                Some(traverse(graph, node.1, solver, bvs))
            } else {
                None
            },
        ),
        _ => unreachable!(),
    }
}

fn traverse<'a>(
    graph: &Formula,
    node: NodeIndex,
    solver: &'a Rc<Btor>,
    bvs: &mut HashMap<NodeIndex, BV<Rc<Btor>>>,
) -> BV<Rc<Btor>> {
    let bv = match &graph[node] {
        Operator(op) => {
            match get_operands(graph, node, solver, bvs) {
                (lhs, Some(rhs)) => {
                    match op {
                        BVOperator::Add => lhs.add(&rhs),
                        BVOperator::Sub => lhs.sub(&rhs),
                        BVOperator::Mul => lhs.mul(&rhs),
                        BVOperator::Equals => lhs._eq(&rhs),
                        BVOperator::BitwiseAnd => lhs.and(&rhs),
                        //BVOperator::GreaterThan => lhs.ugt(&rhs),
                        i => unimplemented!("binary operator: {:?}", i),
                    }
                }
                (lhs, None) => match op {
                    BVOperator::Not => lhs._eq(&BV::from_u64(solver.clone(), 0, 1)),
                    i => unimplemented!("unary operator: {:?}", i),
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
    fn solve(&mut self, graph: &Formula, root: NodeIndex) -> Option<Assignment<BitVector>> {
        solve(graph, root)
    }
}

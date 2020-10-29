use crate::bitvec::BitVector;
use crate::formula_graph::{
    ArgumentSide, BooleanFunction, Formula,
    Node::{Constant, Constraint, Input, Instruction},
};
use crate::solver::{Assignment, Solver};
use boolector::{
    option::{BtorOption, ModelGen, OutputFileFormat},
    Btor, SolverResult, BV,
};
use petgraph::{graph::NodeIndex, Direction};
use riscv_decode::Instruction as Inst;
use std::collections::HashMap;
use std::rc::Rc;

fn get_operands(
    graph: &Formula,
    node: NodeIndex,
    solver: &Rc<Btor>,
    bvs: &mut HashMap<NodeIndex, BV<Rc<Btor>>>,
) -> (BV<Rc<Btor>>, BV<Rc<Btor>>) {
    let mut operands = graph.neighbors_directed(node, Direction::Incoming).detach();

    match operands.next(graph) {
        Some(p) if graph[p.0] == ArgumentSide::Lhs => (
            traverse(graph, p.1, solver, bvs),
            traverse(graph, operands.next(graph).unwrap().1, solver, bvs),
        ),
        Some(p) if graph[p.0] == ArgumentSide::Rhs => (
            traverse(graph, p.1, solver, bvs),
            traverse(graph, operands.next(graph).unwrap().1, solver, bvs),
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
        Instruction(i) => {
            let (lhs, rhs) = get_operands(graph, node, solver, bvs);

            match i.instruction {
                Inst::Add(_) | Inst::Addi(_) => lhs.add(&rhs),
                Inst::Sub(_) => lhs.sub(&rhs),
                Inst::Mul(_) => lhs.mul(&rhs),
                i => unimplemented!("instruction: {:?}", i),
            }
        }
        Constraint(i) => {
            let (lhs, rhs) = get_operands(graph, node, solver, bvs);

            match i.op {
                BooleanFunction::GreaterThan => lhs.ugt(&rhs),
                BooleanFunction::NotEqual => lhs._ne(&rhs),
                BooleanFunction::Equals => lhs._eq(&rhs),
            }
        }
        Input(_i) => BV::new(solver.clone(), 64, None),
        Constant(i) => BV::from_u64(solver.clone(), i.value, 64),
    };

    bvs.insert(node, bv.clone());
    bv
}

fn solve(graph: &Formula, root: NodeIndex) -> Option<Assignment<BitVector>> {
    let solver = Rc::new(Btor::new());
    solver.set_opt(BtorOption::ModelGen(ModelGen::All));
    solver.set_opt(BtorOption::Incremental(true));
    solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));

    if let Constraint(_) = &graph[root] {
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
    } else {
        None
    }
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

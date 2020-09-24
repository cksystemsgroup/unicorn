use crate::bitvec::BitVector;
use crate::formula_graph::{
    ArgumentSide, BooleanFunction, Formula,
    Node::{Constant, Constraint, Input, Instruction},
};
use crate::solver::Assignment;
use boolector::{
    option::{BtorOption, ModelGen, OutputFileFormat},
    Btor, BV,
};
use petgraph::{graph::NodeIndex, Direction};
use riscv_decode::Instruction as Inst;
use std::rc::Rc;

fn get_operands(
    graph: &Formula,
    node: NodeIndex,
    solver: &Rc<Btor>,
) -> (BV<Rc<Btor>>, BV<Rc<Btor>>) {
    let mut operands = graph.neighbors_directed(node, Direction::Incoming).detach();

    match operands.next(graph) {
        Some(p) if graph[p.0] == ArgumentSide::Lhs => (
            traverse(graph, p.1, solver),
            traverse(graph, operands.next(graph).unwrap().1, solver),
        ),
        Some(p) if graph[p.0] == ArgumentSide::Rhs => (
            traverse(graph, p.1, solver),
            traverse(graph, operands.next(graph).unwrap().1, solver),
        ),
        _ => unreachable!(),
    }
}

fn traverse<'a>(graph: &Formula, node: NodeIndex, solver: &'a Rc<Btor>) -> BV<Rc<Btor>> {
    match &graph[node] {
        Instruction(i) => {
            let (lhs, rhs) = get_operands(graph, node, solver);

            match i.instruction {
                Inst::Sub(_i) => lhs.sub(&rhs),
                Inst::Addi(_i) => lhs.add(&rhs),
                Inst::Add(_i) => lhs.add(&rhs),
                Inst::Mul(_i) => lhs.mul(&rhs),
                Inst::Sltu(_i) => unimplemented!("fix this"),
                i => unimplemented!("instruction: {:?}", i),
            }
        }
        Constraint(i) => {
            let (lhs, rhs) = get_operands(graph, node, solver);

            match i.op {
                BooleanFunction::GreaterThan => lhs.ugt(&rhs),
                BooleanFunction::NotEqual => lhs._ne(&rhs),
                BooleanFunction::Equals => lhs._eq(&rhs),
            }
        }
        Input(_i) => BV::new(solver.clone(), 64, None),
        Constant(i) => BV::from_u64(solver.clone(), i.value, 64),
    }
}

pub fn smt(graph: &Formula, root: NodeIndex) -> Option<Assignment<BitVector>> {
    let solver = Rc::new(Btor::new());
    solver.set_opt(BtorOption::ModelGen(ModelGen::All));
    solver.set_opt(BtorOption::Incremental(true));
    solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));

    if let Constraint(_) = &graph[root] {
        traverse(graph, root, &solver).assert();

        println!("result: {:?}\n", solver.sat());
        print!("constraints: \n{}\n", solver.print_constraints());
        print!("assignment: \n{}\n", solver.print_model());
        println!();

        // TODO: Extract assignment from boolector
        Some(vec![])
    } else {
        None
    }
}

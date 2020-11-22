use crate::bitvec::BitVector;
use crate::solver::Solver;
use log::{debug, trace, Level};
pub use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::{
    visit::{VisitMap, Visitable},
    Direction, Graph,
};
use riscu::Instruction;
use std::{collections::HashMap, fmt, rc::Rc};

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
    Not,
    Equals,
    BitwiseAnd,
}

impl BVOperator {
    pub fn is_unary(&self) -> bool {
        *self == BVOperator::Not
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
                BVOperator::Equals => "=",
                BVOperator::BitwiseAnd => "&",
                BVOperator::Sltu => "<",
            }
        )
    }
}

pub enum Query {
    Equals((SymbolId, u64)),
    NotEquals((SymbolId, u64)),
    Reachable,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Node {
    Constant(u64),
    Input(String),
    Operator(BVOperator),
}

pub type Formula = Graph<Node, OperandSide>;
pub type SymbolId = NodeIndex;

fn instruction_to_bv_operator(instruction: Instruction) -> BVOperator {
    match instruction {
        Instruction::Add(_) | Instruction::Addi(_) => BVOperator::Add,
        Instruction::Sub(_) => BVOperator::Sub,
        Instruction::Mul(_) => BVOperator::Mul,
        Instruction::Divu(_) => BVOperator::Divu,
        Instruction::Sltu(_) => BVOperator::Sltu,
        _ => unimplemented!("can not translate {:?} to Operator", instruction),
    }
}

pub fn get_operands(graph: &Formula, sym: SymbolId) -> (SymbolId, Option<SymbolId>) {
    let mut iter = graph.neighbors_directed(sym, Direction::Incoming).detach();

    let lhs = iter
        .next(graph)
        .expect("get_operands() should not be called on operators without operands")
        .1;

    let rhs = iter.next(graph).map(|n| n.1);

    assert!(
        iter.next(graph) == None,
        "operators with arity 1 or 2 are supported only"
    );

    (lhs, rhs)
}

#[derive(Debug)]
pub struct SymbolicState<S>
where
    S: Solver,
{
    data_flow: Graph<Node, OperandSide>,
    path_condition: Option<NodeIndex>,
    solver: Rc<S>,
}

impl<S> Clone for SymbolicState<S>
where
    S: Solver,
{
    fn clone(&self) -> Self {
        Self {
            data_flow: self.data_flow.clone(),
            path_condition: self.path_condition,
            solver: self.solver.clone(),
        }
    }
}

impl<'a, S> SymbolicState<S>
where
    S: Solver,
{
    pub fn new(solver: Rc<S>) -> Self {
        Self {
            data_flow: Graph::new(),
            path_condition: None,
            solver,
        }
    }

    pub fn create_const(&mut self, value: u64) -> SymbolId {
        let constant = Node::Constant(value);

        let i = self.data_flow.add_node(constant);

        trace!("new constant: x{} := {:#x}", i.index(), value);

        i
    }

    pub fn create_operator(
        &mut self,
        instruction: Instruction,
        lhs: SymbolId,
        rhs: SymbolId,
    ) -> SymbolId {
        let op = instruction_to_bv_operator(instruction);
        let n = Node::Operator(op);
        let n_idx = self.data_flow.add_node(n);

        self.connect_operator(lhs, rhs, n_idx);

        trace!(
            "new operator: x{} := x{} {} x{}",
            n_idx.index(),
            lhs.index(),
            op,
            rhs.index()
        );

        n_idx
    }

    pub fn create_input(&mut self, name: &str) -> SymbolId {
        let node = Node::Input(String::from(name));

        let idx = self.data_flow.add_node(node);

        trace!("new input: x{} := {:?}", idx.index(), name);

        idx
    }

    fn append_path_condition(
        &mut self,
        r: NodeIndex,
        mut ns: Vec<NodeIndex>,
        mut es: Vec<EdgeIndex>,
    ) -> (NodeIndex, Vec<NodeIndex>, Vec<EdgeIndex>) {
        if let Some(pc_idx) = self.path_condition {
            let con_idx = self
                .data_flow
                .add_node(Node::Operator(BVOperator::BitwiseAnd));
            let (con_edge_idx1, con_edge_idx2) = self.connect_operator(pc_idx, r, con_idx);

            ns.push(con_idx);
            es.push(con_edge_idx1);
            es.push(con_edge_idx2);

            (con_idx, ns, es)
        } else {
            (r, ns, es)
        }
    }

    fn prepare_query(&mut self, query: Query) -> (NodeIndex, Vec<NodeIndex>, Vec<EdgeIndex>) {
        match query {
            Query::Equals((sym, c)) | Query::NotEquals((sym, c)) => {
                let root_idx = self.data_flow.add_node(Node::Operator(BVOperator::Equals));

                let const_idx = self.data_flow.add_node(Node::Constant(c));
                let const_edge_idx = self
                    .data_flow
                    .add_edge(const_idx, root_idx, OperandSide::Lhs);

                let sym_edge_idx = self.data_flow.add_edge(sym, root_idx, OperandSide::Rhs);

                if let Query::NotEquals(_) = query {
                    let not_idx = self.data_flow.add_node(Node::Operator(BVOperator::Not));
                    let not_edge_idx = self.data_flow.add_edge(root_idx, not_idx, OperandSide::Lhs);

                    self.append_path_condition(
                        root_idx,
                        vec![root_idx, const_idx, not_idx],
                        vec![const_edge_idx, sym_edge_idx, not_edge_idx],
                    )
                } else {
                    self.append_path_condition(
                        root_idx,
                        vec![root_idx, const_idx],
                        vec![const_edge_idx, sym_edge_idx],
                    )
                }
            }
            Query::Reachable => panic!("nothing to be built for that query"),
        }
    }

    fn print_recursive<M: VisitMap<SymbolId>>(&self, n: NodeIndex, visit_map: &mut M) {
        if visit_map.is_visited(&n) {
            return;
        }
        visit_map.visit(n);

        match &self.data_flow[n] {
            Node::Operator(op) => {
                let mut operands = self
                    .data_flow
                    .neighbors_directed(n, Direction::Incoming)
                    .detach();

                if op.is_unary() {
                    let x = operands
                        .next(&self.data_flow)
                        .expect("every unary operator must have 1 operand")
                        .1;

                    self.print_recursive(x, visit_map);

                    debug!("x{} := {}x{}", n.index(), op, x.index());
                } else {
                    let lhs = operands
                        .next(&self.data_flow)
                        .expect("every binary operator must have an lhs operand")
                        .1;

                    let rhs = operands
                        .next(&self.data_flow)
                        .expect("every binary operator must have an rhs operand")
                        .1;

                    self.print_recursive(lhs, visit_map);
                    self.print_recursive(rhs, visit_map);

                    debug!("x{} := x{} {} x{}", n.index(), lhs.index(), op, rhs.index(),)
                }
            }
            Node::Constant(c) => debug!("x{} := {}", n.index(), c),
            Node::Input(name) => debug!("x{} := {:?}", n.index(), name),
        }
    }

    pub fn execute_query(&mut self, query: Query) -> Option<Vec<BitVector>> {
        // prepare graph for query
        let (root, cleanup_nodes, cleanup_edges) = match query {
            Query::Equals(_) | Query::NotEquals(_) => self.prepare_query(query),
            Query::Reachable => {
                if let Some(pc_idx) = self.path_condition {
                    (pc_idx, vec![], vec![])
                } else {
                    // a path without a condition is always reachable
                    debug!("path has no conditon and is therefore reachable");
                    return Some(vec![]);
                }
            }
        };

        if log::log_enabled!(Level::Debug) {
            debug!("query to solve:");
            let mut visited = self.data_flow.visit_map();
            self.print_recursive(root, &mut visited);
            debug!("assert x{} is 1", root.index());
        }

        let result = self.solver.solve(&self.data_flow, root);

        cleanup_edges.iter().for_each(|e| {
            self.data_flow.remove_edge(*e);
        });
        cleanup_nodes.iter().for_each(|n| {
            self.data_flow.remove_node(*n);
        });

        result
    }

    fn connect_operator(
        &mut self,
        lhs: SymbolId,
        rhs: SymbolId,
        op: SymbolId,
    ) -> (EdgeIndex, EdgeIndex) {
        // assert: right hand side edge has to be inserted first
        // solvers depend on edge insertion order!!!
        (
            self.data_flow.add_edge(rhs, op, OperandSide::Rhs),
            self.data_flow.add_edge(lhs, op, OperandSide::Lhs),
        )
    }

    pub fn create_beq_path_condition(&mut self, decision: bool, lhs: SymbolId, rhs: SymbolId) {
        let node = Node::Operator(BVOperator::Equals);
        let mut pc_idx = self.data_flow.add_node(node);

        self.connect_operator(lhs, rhs, pc_idx);

        if !decision {
            let not_idx = self.data_flow.add_node(Node::Operator(BVOperator::Not));

            self.data_flow.add_edge(pc_idx, not_idx, OperandSide::Lhs);

            pc_idx = not_idx;
        }

        if let Some(old_pc_idx) = self.path_condition {
            let con_idx = self
                .data_flow
                .add_node(Node::Operator(BVOperator::BitwiseAnd));

            self.connect_operator(old_pc_idx, pc_idx, con_idx);

            pc_idx = con_idx;
        }

        self.path_condition = Some(pc_idx);
    }

    pub fn get_input_assignments(&self, assignment: &[BitVector]) -> HashMap<String, BitVector> {
        self.data_flow
            .node_indices()
            .filter_map(|idx| match self.data_flow[idx].clone() {
                Node::Input(name) => Some((name, assignment[idx.index()])),
                _ => None,
            })
            .collect()
    }
}

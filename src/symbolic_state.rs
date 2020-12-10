use crate::{
    bitvec::BitVector,
    bug::Witness,
    solver::{Solver, SolverError},
};
use log::{debug, trace, Level};
pub use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::{Direction, Graph};
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

    pub fn create_instruction(
        &mut self,
        instruction: Instruction,
        lhs: SymbolId,
        rhs: SymbolId,
    ) -> SymbolId {
        let op = instruction_to_bv_operator(instruction);

        let root = self.create_operator(op, lhs, rhs);

        // constrain divisor to be not zero,
        // as division by zero is allowed in SMT bit-vector formulas
        if matches!(op, BVOperator::Divu)
            && matches!(self.data_flow[rhs], Node::Operator(_) | Node::Input(_))
        {
            let zero = self.create_const(0);
            let negated_condition = self.create_operator(BVOperator::Equals, rhs, zero);
            let condition = self.create_unary_operator(BVOperator::Not, negated_condition);

            self.add_path_condition(condition);
        }

        root
    }

    pub fn create_operator(&mut self, op: BVOperator, lhs: SymbolId, rhs: SymbolId) -> SymbolId {
        assert!(op.is_binary(), "has to be a binary operator");

        let n = Node::Operator(op);
        let n_idx = self.data_flow.add_node(n);

        assert!(!(
                matches!(self.data_flow[lhs], Node::Constant(_))
                && matches!(self.data_flow[rhs], Node::Constant(_))
            ),
            "every operand has to be derived from an input or has to be an (already folded) constant"
        );

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

    fn create_unary_operator(&mut self, op: BVOperator, v: SymbolId) -> SymbolId {
        assert!(op.is_unary(), "has to be a unary operator");

        let op_id = self.data_flow.add_node(Node::Operator(op));

        self.data_flow.add_edge(v, op_id, OperandSide::Lhs);

        op_id
    }

    pub fn create_input(&mut self, name: &str) -> SymbolId {
        let node = Node::Input(String::from(name));

        let idx = self.data_flow.add_node(node);

        trace!("new input: x{} := {:?}", idx.index(), name);

        idx
    }

    pub fn create_beq_path_condition(&mut self, decision: bool, lhs: SymbolId, rhs: SymbolId) {
        let mut pc_idx = self.create_operator(BVOperator::Equals, lhs, rhs);

        if !decision {
            pc_idx = self.create_unary_operator(BVOperator::Not, pc_idx);
        }

        self.add_path_condition(pc_idx)
    }

    fn add_path_condition(&mut self, condition: SymbolId) {
        let new_condition = if let Some(old_condition) = self.path_condition {
            self.create_operator(BVOperator::BitwiseAnd, old_condition, condition)
        } else {
            condition
        };

        self.path_condition = Some(new_condition);
    }

    pub fn execute_query(&mut self, query: Query) -> Result<Option<Witness>, SolverError> {
        // prepare graph for query
        let (root, cleanup_nodes, cleanup_edges) = match query {
            Query::Equals(_) | Query::NotEquals(_) => self.prepare_query(query),
            Query::Reachable => {
                if let Some(pc_idx) = self.path_condition {
                    (pc_idx, vec![], vec![])
                } else {
                    // a path without a condition is always reachable
                    debug!("path has no conditon and is therefore reachable");

                    return Ok(Some(self.build_trivial_witness()));
                }
            }
        };

        if log::log_enabled!(Level::Debug) {
            debug!("query to solve:");

            let root_idx = self.print_recursive(root);

            debug!("assert x{} is 1", root_idx.index());
        }

        let result = match self.solver.solve(&self.data_flow, root) {
            Ok(Some(ref assignment)) => Ok(Some(self.build_witness(root, assignment))),
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        };

        cleanup_edges.iter().for_each(|e| {
            self.data_flow.remove_edge(*e);
        });
        cleanup_nodes.iter().for_each(|n| {
            self.data_flow.remove_node(*n);
        });

        result
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
                        not_idx,
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
            Query::Reachable => panic!("nothing to be prepeared for that query"),
        }
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

    fn print_recursive(&self, root: NodeIndex) -> NodeIndex {
        let mut visited = HashMap::<NodeIndex, NodeIndex>::new();
        let mut printer = Printer {};

        self.traverse(root, &mut visited, &mut printer)
    }

    fn build_trivial_witness(&self) -> Witness {
        let mut witness = Witness::new();

        self.data_flow.node_indices().for_each(|idx| {
            if let Node::Input(name) = &self.data_flow[idx] {
                witness.add_variable(name.as_str(), BitVector(0));
            }
        });

        witness
    }

    fn build_witness(&self, root: NodeIndex, assignment: &[BitVector]) -> Witness {
        let mut visited = HashMap::<NodeIndex, usize>::new();

        let mut witness = Witness::new();
        let mut builder = WitnessBuilder {
            witness: &mut witness,
            assignment,
        };

        self.traverse(root, &mut visited, &mut builder);

        witness
    }

    fn traverse<V, R>(&self, n: NodeIndex, visit_map: &mut HashMap<NodeIndex, R>, v: &mut V) -> R
    where
        V: Visitor<R>,
        R: Copy,
    {
        if let Some(result) = visit_map.get(&n) {
            return *result;
        }

        let result = match &self.data_flow[n] {
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

                    let x = self.traverse(x, visit_map, v);

                    v.unary(n, *op, x)
                } else {
                    let lhs = operands
                        .next(&self.data_flow)
                        .expect("every binary operator must have an lhs operand")
                        .1;

                    let rhs = operands
                        .next(&self.data_flow)
                        .expect("every binary operator must have an rhs operand")
                        .1;

                    let lhs = self.traverse(lhs, visit_map, v);
                    let rhs = self.traverse(rhs, visit_map, v);

                    v.binary(n, *op, lhs, rhs)
                }
            }
            Node::Constant(c) => v.constant(n, BitVector(*c)),
            Node::Input(name) => v.input(n, name),
        };

        visit_map.insert(n, result);

        result
    }
}

trait Visitor<T> {
    fn input(&mut self, idx: NodeIndex, name: &str) -> T;
    fn constant(&mut self, idx: NodeIndex, v: BitVector) -> T;
    fn unary(&mut self, idx: NodeIndex, op: BVOperator, v: T) -> T;
    fn binary(&mut self, idx: NodeIndex, op: BVOperator, lhs: T, rhs: T) -> T;
}

struct Printer {}

impl Visitor<NodeIndex> for Printer {
    fn input(&mut self, idx: NodeIndex, name: &str) -> NodeIndex {
        debug!("x{} := {:?}", idx.index(), name);
        idx
    }
    fn constant(&mut self, idx: NodeIndex, v: BitVector) -> NodeIndex {
        debug!("x{} := {}", idx.index(), v.0);
        idx
    }
    fn unary(&mut self, idx: NodeIndex, op: BVOperator, v: NodeIndex) -> NodeIndex {
        debug!("x{} := {}x{}", idx.index(), op, v.index());
        idx
    }
    fn binary(
        &mut self,
        idx: NodeIndex,
        op: BVOperator,
        lhs: NodeIndex,
        rhs: NodeIndex,
    ) -> NodeIndex {
        debug!(
            "x{} := x{} {} x{}",
            idx.index(),
            lhs.index(),
            op,
            rhs.index()
        );
        idx
    }
}

struct WitnessBuilder<'a> {
    witness: &'a mut Witness,
    assignment: &'a [BitVector],
}

impl<'a> Visitor<usize> for WitnessBuilder<'a> {
    fn input(&mut self, idx: NodeIndex, name: &str) -> usize {
        self.witness
            .add_variable(name, self.assignment[idx.index()])
    }
    fn constant(&mut self, _idx: NodeIndex, v: BitVector) -> usize {
        self.witness.add_constant(v)
    }
    fn unary(&mut self, idx: NodeIndex, op: BVOperator, v: usize) -> usize {
        self.witness.add_unary(op, v, self.assignment[idx.index()])
    }
    fn binary(&mut self, idx: NodeIndex, op: BVOperator, lhs: usize, rhs: usize) -> usize {
        self.witness
            .add_binary(lhs, op, rhs, self.assignment[idx.index()])
    }
}

use crate::solver::{
    BVOperator, BitVector, Formula, FormulaVisitor, OperandSide, Solver, SolverError, Symbol,
    SymbolId,
};
use log::{debug, trace, Level};
pub use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::{
    dot::Dot,
    graph::{Neighbors, NodeIndices},
    Direction,
};
use riscu::Instruction;
use std::{collections::HashMap, fmt, ops::Index};

#[derive(Debug)]
pub enum QueryResult {
    Sat(Witness),
    UnSat,
    Unknown,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Condition {
    Equals,
    NotEquals,
}

pub type SymbolicValue = NodeIndex;
pub type DataFlowGraph = petgraph::Graph<Symbol, OperandSide>;

fn instruction_to_bv_operator(instruction: Instruction) -> BVOperator {
    match instruction {
        Instruction::Add(_) | Instruction::Addi(_) => BVOperator::Add,
        Instruction::Sub(_) => BVOperator::Sub,
        Instruction::Mul(_) => BVOperator::Mul,
        Instruction::Divu(_) => BVOperator::Divu,
        Instruction::Remu(_) => BVOperator::Remu,
        Instruction::Sltu(_) => BVOperator::Sltu,
        _ => unimplemented!("can not translate {:?} to Operator", instruction),
    }
}

#[derive(Debug)]
pub struct SymbolicState<'a, S>
where
    S: Solver,
{
    data_flow: DataFlowGraph,
    path_condition: SymbolicValue,
    solver: &'a S,
    zero: SymbolicValue,
    one: SymbolicValue,
    tmp_nodes: Option<Vec<NodeIndex>>,
    tmp_edges: Option<Vec<EdgeIndex>>,
}

impl<'a, S> Clone for SymbolicState<'a, S>
where
    S: Solver,
{
    fn clone(&self) -> Self {
        Self {
            data_flow: self.data_flow.clone(),
            path_condition: self.path_condition,
            solver: self.solver,
            zero: self.zero,
            one: self.one,
            tmp_nodes: self.tmp_nodes.clone(),
            tmp_edges: self.tmp_edges.clone(),
        }
    }
}

impl<'a, S> SymbolicState<'a, S>
where
    S: Solver,
{
    pub fn new(solver: &'a S) -> Self {
        let mut data_flow = DataFlowGraph::new();

        // some useful constants
        let zero = data_flow.add_node(Symbol::Constant(BitVector(0)));
        let one = data_flow.add_node(Symbol::Constant(BitVector(1)));

        // path condition is true by default
        let path_condition = one;

        Self {
            data_flow,
            path_condition,
            solver,
            zero,
            one,
            tmp_nodes: None,
            tmp_edges: None,
        }
    }

    fn add_node(&mut self, weight: Symbol) -> SymbolicValue {
        let idx = self.data_flow.add_node(weight);

        if let Some(ref mut tmp_nodes) = self.tmp_nodes {
            tmp_nodes.push(idx);
        }

        idx
    }

    fn add_edge(&mut self, from: SymbolicValue, to: SymbolicValue, side: OperandSide) -> EdgeIndex {
        let idx = self.data_flow.add_edge(from, to, side);

        if let Some(ref mut tmp_edges) = self.tmp_edges {
            tmp_edges.push(idx);
        }

        idx
    }

    pub fn create_const(&mut self, value: u64) -> SymbolicValue {
        let i = match value {
            0 => self.zero(),
            1 => self.one(),
            _ => self.add_node(Symbol::Constant(BitVector(value))),
        };

        trace!("new constant: x{} := {:#x}", i.index(), value);

        i
    }

    pub fn zero(&self) -> SymbolicValue {
        self.zero
    }

    pub fn one(&self) -> SymbolicValue {
        self.one
    }

    pub fn create_instruction(
        &mut self,
        instruction: Instruction,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) -> SymbolicValue {
        let op = instruction_to_bv_operator(instruction);

        self.create_operator(op, lhs, rhs)
    }

    pub fn create_operator(
        &mut self,
        op: BVOperator,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) -> SymbolicValue {
        assert!(op.is_binary(), "has to be a binary operator");

        let n = Symbol::Operator(op);
        let n_idx = self.add_node(n);

        assert!(!(
                matches!(self.data_flow[lhs], Symbol::Constant(_))
                && matches!(self.data_flow[rhs], Symbol::Constant(_))
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

    fn create_unary_operator(&mut self, op: BVOperator, v: SymbolicValue) -> SymbolicValue {
        assert!(op.is_unary(), "has to be a unary operator");

        let op_id = self.add_node(Symbol::Operator(op));

        self.add_edge(v, op_id, OperandSide::Lhs);

        op_id
    }

    pub fn create_input(&mut self, name: &str) -> SymbolicValue {
        let node = Symbol::Input(String::from(name));

        let idx = self.add_node(node);

        trace!("new input: x{} := {:?}", idx.index(), name);

        idx
    }

    pub fn add_path_condition(&mut self, cond: Condition, lhs: SymbolicValue, rhs: SymbolicValue) {
        let condition = match cond {
            Condition::Equals => self.create_operator(BVOperator::Equals, lhs, rhs),
            Condition::NotEquals => {
                let op = self.create_operator(BVOperator::Equals, lhs, rhs);

                self.create_unary_operator(BVOperator::Not, op)
            }
        };

        self.path_condition =
            self.create_operator(BVOperator::BitwiseAnd, self.path_condition, condition);
    }

    pub fn with_temp_conditions<F, R>(&mut self, f: F) -> R
    where
        F: Fn(&mut Self) -> R,
    {
        self.tmp_nodes = Some(Vec::new());
        self.tmp_edges = Some(Vec::new());

        let result = f(self);

        self.tmp_edges
            .as_ref()
            .expect("a list of edges to clean up has to exist here")
            .clone() // TODO: probably we could somehow get rid of this clone
            .iter()
            .for_each(|e| {
                self.data_flow.remove_edge(*e);
            });

        self.tmp_edges = None;

        self.tmp_nodes
            .as_ref()
            .expect("a list of nodes to clean up has to exist here")
            .clone() // TODO: probably we could somehow get rid of this clone
            .iter()
            .for_each(|n| {
                self.data_flow.remove_node(*n);
            });

        self.tmp_nodes = None;

        result
    }

    pub fn reachable(&mut self) -> Result<QueryResult, SolverError> {
        let formula = FormulaView::new(&self.data_flow, self.path_condition);

        if log::log_enabled!(Level::Debug) {
            debug!("query to solve:");

            let root = formula.print_recursive();

            debug!("assert x{} is 1", root);
        }

        match self.solver.solve(&formula) {
            Ok(Some(ref assignment)) => Ok(QueryResult::Sat(formula.build_witness(assignment))),
            Ok(None) => Ok(QueryResult::UnSat),
            Err(SolverError::SatUnknown) | Err(SolverError::Timeout) => Ok(QueryResult::Unknown),
            Err(e) => Err(e),
        }
    }

    pub fn reachable_with(
        &mut self,
        cond: Condition,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) -> Result<QueryResult, SolverError> {
        self.with_temp_conditions(|this| {
            let root_idx = this.create_operator(BVOperator::Equals, lhs, rhs);

            let root_idx = if Condition::NotEquals == cond {
                this.create_unary_operator(BVOperator::Not, root_idx)
            } else {
                root_idx
            };

            let and_idx =
                this.create_operator(BVOperator::BitwiseAnd, this.path_condition, root_idx);

            let pc = this.path_condition;
            this.path_condition = and_idx;

            let result = this.reachable();

            this.path_condition = pc;

            result
        })
    }

    fn connect_operator(
        &mut self,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
        op: SymbolicValue,
    ) -> (EdgeIndex, EdgeIndex) {
        // assert: right hand side edge has to be inserted first
        // solvers depend on edge insertion order!!!
        (
            self.add_edge(rhs, op, OperandSide::Rhs),
            self.add_edge(lhs, op, OperandSide::Lhs),
        )
    }
}

impl<'a, S: Solver> fmt::Display for SymbolicState<'a, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dot_graph = Dot::with_config(&self.data_flow, &[]);

        write!(f, "{:?}", dot_graph)
    }
}

pub struct FormulaView<'a> {
    data_flow: &'a DataFlowGraph,
    root: SymbolicValue,
}

impl<'a> FormulaView<'a> {
    pub fn new(data_flow: &'a DataFlowGraph, root: SymbolicValue) -> Self {
        Self { data_flow, root }
    }

    pub fn print_recursive(&self) -> SymbolId {
        let mut visited = HashMap::<SymbolId, SymbolId>::new();
        let mut printer = Printer {};

        self.traverse(self.root(), &mut visited, &mut printer)
    }

    fn build_witness(&self, assignment: &HashMap<SymbolId, BitVector>) -> Witness {
        let mut visited = HashMap::<SymbolId, usize>::new();

        let mut witness = Witness::new();
        let mut builder = WitnessBuilder {
            witness: &mut witness,
            assignment,
        };

        self.traverse(self.root(), &mut visited, &mut builder);

        witness
    }
}

impl<'a> Index<SymbolId> for FormulaView<'a> {
    type Output = Symbol;

    fn index(&self, idx: SymbolId) -> &Self::Output {
        &self.data_flow[NodeIndex::new(idx)]
    }
}

impl<'a> Formula for FormulaView<'a> {
    type DependencyIter = std::iter::Map<Neighbors<'a, OperandSide>, fn(NodeIndex) -> usize>;
    type SymbolIdsIter = std::iter::Map<NodeIndices, fn(NodeIndex) -> usize>;

    fn root(&self) -> SymbolId {
        self.root.index()
    }

    fn operands(&self, sym: SymbolId) -> (SymbolId, Option<SymbolId>) {
        let mut iter = self
            .data_flow
            .neighbors_directed(NodeIndex::new(sym), Direction::Incoming)
            .detach();

        let lhs = iter
            .next(self.data_flow)
            .expect("get_operands() should not be called on operators without operands")
            .1
            .index();

        let rhs = iter.next(self.data_flow).map(|n| n.1.index());

        assert!(
            iter.next(self.data_flow) == None,
            "operators with arity 1 or 2 are supported only"
        );

        (lhs, rhs)
    }

    fn operand(&self, sym: SymbolId) -> SymbolId {
        self.data_flow
            .edges_directed(NodeIndex::new(sym), Direction::Incoming)
            .next()
            .expect("every unary operator must have an operand")
            .source()
            .index()
    }

    fn dependencies(&self, sym: SymbolId) -> Self::DependencyIter {
        self.data_flow
            .neighbors_directed(NodeIndex::new(sym), Direction::Outgoing)
            .map(|idx| idx.index())
    }

    fn symbol_ids(&self) -> Self::SymbolIdsIter {
        self.data_flow.node_indices().map(|i| i.index())
    }

    fn is_operand(&self, sym: SymbolId) -> bool {
        !matches!(self.data_flow[NodeIndex::new(sym)], Symbol::Operator(_))
    }

    fn traverse<V, R>(&self, n: SymbolId, visit_map: &mut HashMap<SymbolId, R>, v: &mut V) -> R
    where
        V: FormulaVisitor<R>,
        R: Clone,
    {
        if let Some(result) = visit_map.get(&n) {
            return (*result).clone();
        }

        let result = match &self.data_flow[NodeIndex::new(n)] {
            Symbol::Operator(op) => {
                let mut operands = self
                    .data_flow
                    .neighbors_directed(NodeIndex::new(n), Direction::Incoming)
                    .detach();

                if op.is_unary() {
                    let x = operands
                        .next(self.data_flow)
                        .expect("every unary operator must have 1 operand")
                        .1
                        .index();

                    let x = self.traverse(x, visit_map, v);

                    v.unary(n, *op, x)
                } else {
                    let lhs = operands
                        .next(self.data_flow)
                        .expect("every binary operator must have an lhs operand")
                        .1
                        .index();

                    let rhs = operands
                        .next(self.data_flow)
                        .expect("every binary operator must have an rhs operand")
                        .1
                        .index();

                    let lhs = self.traverse(lhs, visit_map, v);
                    let rhs = self.traverse(rhs, visit_map, v);

                    v.binary(n, *op, lhs, rhs)
                }
            }
            Symbol::Constant(c) => v.constant(n, *c),
            Symbol::Input(name) => v.input(n, name.as_str()),
        };

        visit_map.insert(n, result.clone());

        result
    }
}

struct Printer {}

impl<'a> FormulaVisitor<SymbolId> for Printer {
    fn input(&mut self, idx: SymbolId, name: &str) -> SymbolId {
        debug!("x{} := {:?}", idx, name);
        idx
    }
    fn constant(&mut self, idx: SymbolId, v: BitVector) -> SymbolId {
        debug!("x{} := {}", idx, v.0);
        idx
    }
    fn unary(&mut self, idx: SymbolId, op: BVOperator, v: SymbolId) -> SymbolId {
        debug!("x{} := {}x{}", idx, op, v);
        idx
    }
    fn binary(&mut self, idx: SymbolId, op: BVOperator, lhs: SymbolId, rhs: SymbolId) -> SymbolId {
        debug!("x{} := x{} {} x{}", idx, lhs, op, rhs);
        idx
    }
}

struct WitnessBuilder<'a> {
    witness: &'a mut Witness,
    assignment: &'a HashMap<SymbolId, BitVector>,
}

impl<'a> FormulaVisitor<usize> for WitnessBuilder<'a> {
    fn input(&mut self, idx: SymbolId, name: &str) -> usize {
        self.witness.add_variable(
            name,
            *self
                .assignment
                .get(&idx)
                .expect("assignment should be available"),
        )
    }
    fn constant(&mut self, _idx: SymbolId, v: BitVector) -> usize {
        self.witness.add_constant(v)
    }
    fn unary(&mut self, idx: SymbolId, op: BVOperator, v: usize) -> usize {
        self.witness.add_unary(
            op,
            v,
            *self
                .assignment
                .get(&idx)
                .expect("assignment should be available"),
        )
    }
    fn binary(&mut self, idx: SymbolId, op: BVOperator, lhs: usize, rhs: usize) -> usize {
        self.witness.add_binary(
            lhs,
            op,
            rhs,
            *self
                .assignment
                .get(&idx)
                .expect("assignment should be available"),
        )
    }
}

#[derive(Debug, Clone)]
pub(crate) enum Term {
    Constant(u64),
    Variable(String, u64),
    Unary(BVOperator, usize, u64),
    Binary(usize, BVOperator, usize, u64),
}

#[derive(Debug, Clone)]
pub struct Witness {
    assignments: Vec<Term>,
}

impl Default for Witness {
    fn default() -> Self {
        Self {
            assignments: Vec::new(),
        }
    }
}

impl Witness {
    pub fn new() -> Self {
        Witness::default()
    }

    pub fn add_constant(&mut self, value: BitVector) -> usize {
        self.assignments.push(Term::Constant(value.0));

        self.assignments.len() - 1
    }

    pub fn add_variable(&mut self, name: &str, result: BitVector) -> usize {
        self.assignments
            .push(Term::Variable(name.to_owned(), result.0));

        self.assignments.len() - 1
    }

    pub fn add_unary(&mut self, op: BVOperator, v: usize, result: BitVector) -> usize {
        self.assignments.push(Term::Unary(op, v, result.0));

        self.assignments.len() - 1
    }

    pub fn add_binary(
        &mut self,
        lhs: usize,
        op: BVOperator,
        rhs: usize,
        result: BitVector,
    ) -> usize {
        self.assignments.push(Term::Binary(lhs, op, rhs, result.0));

        self.assignments.len() - 1
    }
}

impl fmt::Display for Witness {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "[").and_then(|_| {
            self.assignments
                .clone()
                .into_iter()
                .enumerate()
                .try_for_each(|(id, a)| match a {
                    Term::Constant(c) => writeln!(f, "  x{} := {},", id, c),
                    Term::Variable(name, v) => writeln!(f, "  x{} := {:?} ({}),", id, name, v),
                    Term::Unary(op, x, v) => writeln!(f, "  x{} := {}x{} ({}),", id, op, x, v),
                    Term::Binary(lhs, op, rhs, v) => {
                        writeln!(f, "  x{} := x{} {} x{} ({}),", id, lhs, op, rhs, v)
                    }
                })
                .and_then(|_| write!(f, "]"))
        })
    }
}

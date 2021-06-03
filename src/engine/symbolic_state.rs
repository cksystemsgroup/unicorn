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

pub enum Query {
    Equals((SymbolicValue, u64)),
    NotEquals((SymbolicValue, u64)),
    Reachable,
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
        }
    }
}

impl<'a, S> SymbolicState<'a, S>
where
    S: Solver,
{
    pub fn new(solver: &'a S) -> Self {
        let mut data_flow = DataFlowGraph::new();

        let constant = Symbol::Constant(BitVector(1));

        let path_condition = data_flow.add_node(constant);

        Self {
            data_flow,
            path_condition,
            solver,
        }
    }

    pub fn create_const(&mut self, value: u64) -> SymbolicValue {
        let constant = Symbol::Constant(BitVector(value));

        let i = self.data_flow.add_node(constant);

        trace!("new constant: x{} := {:#x}", i.index(), value);

        i
    }

    pub fn create_instruction(
        &mut self,
        instruction: Instruction,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) -> SymbolicValue {
        let op = instruction_to_bv_operator(instruction);

        let root = self.create_operator(op, lhs, rhs);

        // constrain divisor to be not zero,
        // as division by zero is allowed in SMT bit-vector formulas
        if matches!(op, BVOperator::Divu)
            && matches!(self.data_flow[rhs], Symbol::Operator(_) | Symbol::Input(_))
        {
            let zero = self.create_const(0);
            let negated_condition = self.create_operator(BVOperator::Equals, rhs, zero);
            let condition = self.create_unary_operator(BVOperator::Not, negated_condition);

            self.add_path_condition(condition);
        }

        root
    }

    pub fn create_operator(
        &mut self,
        op: BVOperator,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) -> SymbolicValue {
        assert!(op.is_binary(), "has to be a binary operator");

        let n = Symbol::Operator(op);
        let n_idx = self.data_flow.add_node(n);

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

        let op_id = self.data_flow.add_node(Symbol::Operator(op));

        self.data_flow.add_edge(v, op_id, OperandSide::Lhs);

        op_id
    }

    pub fn create_input(&mut self, name: &str) -> SymbolicValue {
        let node = Symbol::Input(String::from(name));

        let idx = self.data_flow.add_node(node);

        trace!("new input: x{} := {:?}", idx.index(), name);

        idx
    }

    pub fn create_beq_path_condition(
        &mut self,
        decision: bool,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) {
        let mut pc_idx = self.create_operator(BVOperator::Equals, lhs, rhs);

        if !decision {
            pc_idx = self.create_unary_operator(BVOperator::Not, pc_idx);
        }

        self.add_path_condition(pc_idx)
    }

    fn add_path_condition(&mut self, condition: SymbolicValue) {
        self.path_condition =
            self.create_operator(BVOperator::BitwiseAnd, self.path_condition, condition);
    }

    pub fn execute_query(&mut self, query: Query) -> Result<Option<Witness>, SolverError> {
        // prepare graph for query
        let (root, cleanup_nodes, cleanup_edges) = match query {
            Query::Equals(_) | Query::NotEquals(_) => self.prepare_query(query),
            Query::Reachable => (self.path_condition, vec![], vec![]),
        };

        let formula = FormulaView::new(&self.data_flow, root);

        if log::log_enabled!(Level::Debug) {
            debug!("query to solve:");

            let root = formula.print_recursive();

            debug!("assert x{} is 1", root);
        }

        let result = match self.solver.solve(&formula) {
            Ok(Some(ref assignment)) => Ok(Some(formula.build_witness(assignment))),
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
        r: SymbolicValue,
        mut ns: Vec<SymbolicValue>,
        mut es: Vec<EdgeIndex>,
    ) -> (SymbolicValue, Vec<SymbolicValue>, Vec<EdgeIndex>) {
        let con_idx = self
            .data_flow
            .add_node(Symbol::Operator(BVOperator::BitwiseAnd));
        let (con_edge_idx1, con_edge_idx2) = self.connect_operator(self.path_condition, r, con_idx);

        ns.push(con_idx);
        es.push(con_edge_idx1);
        es.push(con_edge_idx2);

        (con_idx, ns, es)
    }

    fn prepare_query(
        &mut self,
        query: Query,
    ) -> (SymbolicValue, Vec<SymbolicValue>, Vec<EdgeIndex>) {
        match query {
            Query::Equals((sym, c)) | Query::NotEquals((sym, c)) => {
                let root_idx = self
                    .data_flow
                    .add_node(Symbol::Operator(BVOperator::Equals));

                let const_idx = self.data_flow.add_node(Symbol::Constant(BitVector(c)));
                let const_edge_idx = self
                    .data_flow
                    .add_edge(const_idx, root_idx, OperandSide::Lhs);

                let sym_edge_idx = self.data_flow.add_edge(sym, root_idx, OperandSide::Rhs);

                if let Query::NotEquals(_) = query {
                    let not_idx = self.data_flow.add_node(Symbol::Operator(BVOperator::Not));
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
        lhs: SymbolicValue,
        rhs: SymbolicValue,
        op: SymbolicValue,
    ) -> (EdgeIndex, EdgeIndex) {
        // assert: right hand side edge has to be inserted first
        // solvers depend on edge insertion order!!!
        (
            self.data_flow.add_edge(rhs, op, OperandSide::Rhs),
            self.data_flow.add_edge(lhs, op, OperandSide::Lhs),
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
                .and_then(|_| writeln!(f, "]"))
        })
    }
}

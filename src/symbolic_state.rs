use crate::bitvec::BitVector;
use crate::solver::Solver;
pub use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::Graph;
use riscv_decode::Instruction;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Clone, Debug, Copy, Eq, Hash, PartialEq)]
pub enum ArgumentSide {
    Lhs,
    Rhs,
}

impl ArgumentSide {
    #[allow(dead_code)]
    pub fn other(&self) -> Self {
        match self {
            ArgumentSide::Lhs => ArgumentSide::Rhs,
            ArgumentSide::Rhs => ArgumentSide::Lhs,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum BVOperator {
    Add,
    Sub,
    Mul,
    Divu,
    Not,
    Equals,
    BitwiseAnd,
}

impl BVOperator {
    pub fn is_unary(&self) -> bool {
        *self == BVOperator::Not
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

pub type SymbolId = NodeIndex;

fn instruction_to_bv_operator(instruction: Instruction) -> BVOperator {
    match instruction {
        Instruction::Add(_) | Instruction::Addi(_) => BVOperator::Add,
        Instruction::Sub(_) => BVOperator::Sub,
        Instruction::Mul(_) => BVOperator::Mul,
        Instruction::Divu(_) => BVOperator::Divu,
        _ => unimplemented!("can not translate {:?} to Operator", instruction),
    }
}

pub type Formula = Graph<Node, ArgumentSide>;

#[derive(Debug)]
pub struct SymbolicState<S>
where
    S: Solver,
{
    data_flow: Graph<Node, ArgumentSide>,
    path_condition: Option<NodeIndex>,
    solver: Rc<RefCell<S>>,
}

impl<S> Clone for SymbolicState<S>
where
    S: Solver,
{
    fn clone(&self) -> Self {
        Self {
            data_flow: self.data_flow.clone(),
            path_condition: self.path_condition,
            solver: Rc::clone(&self.solver),
        }
    }
}

impl<'a, S> SymbolicState<S>
where
    S: Solver,
{
    pub fn new(solver: Rc<RefCell<S>>) -> Self {
        Self {
            data_flow: Graph::new(),
            path_condition: None,
            solver,
        }
    }

    pub fn create_const(&mut self, value: u64) -> SymbolId {
        let constant = Node::Constant(value);

        self.data_flow.add_node(constant)
    }

    pub fn create_operator(
        &mut self,
        instruction: Instruction,
        lhs: SymbolId,
        rhs: SymbolId,
    ) -> SymbolId {
        let op = Node::Operator(instruction_to_bv_operator(instruction));
        let op_idx = self.data_flow.add_node(op);

        self.data_flow.add_edge(lhs, op_idx, ArgumentSide::Lhs);
        self.data_flow.add_edge(rhs, op_idx, ArgumentSide::Rhs);

        op_idx
    }

    pub fn create_input(&mut self, name: &str) -> SymbolId {
        let node = Node::Input(String::from(name));

        self.data_flow.add_node(node)
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
            let con_edge_idx1 = self.data_flow.add_edge(pc_idx, con_idx, ArgumentSide::Lhs);
            let con_edge_idx2 = self.data_flow.add_edge(r, con_idx, ArgumentSide::Rhs);

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
                let const_edge_idx =
                    self.data_flow
                        .add_edge(const_idx, root_idx, ArgumentSide::Lhs);

                let sym_edge_idx = self.data_flow.add_edge(sym, root_idx, ArgumentSide::Rhs);

                if let Query::NotEquals(_) = query {
                    let not_idx = self.data_flow.add_node(Node::Operator(BVOperator::Not));
                    let not_edge_idx =
                        self.data_flow
                            .add_edge(root_idx, not_idx, ArgumentSide::Lhs);

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

    pub fn execute_query(&mut self, query: Query) -> Option<Vec<BitVector>> {
        // prepare graph for query
        let (root, cleanup_nodes, cleanup_edges) = match query {
            Query::Equals(_) | Query::NotEquals(_) => self.prepare_query(query),
            Query::Reachable => {
                if let Some(pc_idx) = self.path_condition {
                    (pc_idx, vec![], vec![])
                } else {
                    // a path without a condition is always reachable
                    return Some(vec![]);
                }
            }
        };

        let result = self.solver.borrow_mut().solve(&self.data_flow, root);

        cleanup_edges.iter().for_each(|e| {
            self.data_flow.remove_edge(*e);
        });
        cleanup_nodes.iter().for_each(|n| {
            self.data_flow.remove_node(*n);
        });

        result
    }

    pub fn create_beq_path_condition(&mut self, decision: bool, lhs: SymbolId, rhs: SymbolId) {
        let node = Node::Operator(BVOperator::Equals);
        let mut pc_idx = self.data_flow.add_node(node);

        self.data_flow.add_edge(lhs, pc_idx, ArgumentSide::Lhs);
        self.data_flow.add_edge(rhs, pc_idx, ArgumentSide::Rhs);

        if !decision {
            let not_idx = self.data_flow.add_node(Node::Operator(BVOperator::Not));

            self.data_flow.add_edge(pc_idx, not_idx, ArgumentSide::Lhs);

            pc_idx = not_idx;
        }

        if let Some(old_pc_idx) = self.path_condition {
            let con_idx = self
                .data_flow
                .add_node(Node::Operator(BVOperator::BitwiseAnd));

            self.data_flow
                .add_edge(old_pc_idx, con_idx, ArgumentSide::Lhs);
            self.data_flow.add_edge(pc_idx, con_idx, ArgumentSide::Rhs);

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

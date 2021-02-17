//! # Handle control flow graphs
//!
//! This module defines and handles control flow graphs.
//!
//! There are three different kind of edges:
//! - trivial edges (`pc = pc + 4;`)
//!   - any non control flow instruction
//!   - `beq`: false edge
//! - pure edges
//!   - `beq`: true edge
//!   - `jal`: when link not used (=> `rd` is zero)
//! - stateful edges
//!   - `jal`: when link is used (=> `rd` is `ra`)
//!   - `jalr`

use anyhow::{ensure, Context, Error, Result};
use byteorder::{ByteOrder, LittleEndian};
use petgraph::{
    dot::Dot,
    graph::{EdgeIndex, NodeIndex},
    visit::EdgeRef,
};
use riscu::{decode, Instruction, Program, Register};
use std::{fmt, mem::size_of, vec::Vec};

type Edge = (NodeIndex, NodeIndex, Option<ProcedureCallId>);

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ProcedureCallId {
    Call(u64),
    Return(u64),
}

pub type Graph = petgraph::Graph<Instruction, Option<ProcedureCallId>>;

pub struct ControlFlowGraph {
    pub graph: Graph,
    pub start: NodeIndex,
    pub exit: NodeIndex,
}

impl ControlFlowGraph {
    pub fn build_for(program: &Program) -> Result<ControlFlowGraph> {
        let mut graph = create_instruction_graph(program)?;

        fn add_edges(graph: &mut Graph, edges: &[Edge]) {
            edges.iter().for_each(|e| {
                graph.add_edge(e.0, e.1, e.2);
            });
        }

        let edges = compute_edges(&graph, construct_edge_if_trivial);
        add_edges(&mut graph, &edges);

        let pure_edges = compute_edges(&graph, construct_edge_if_pure);
        add_edges(&mut graph, &pure_edges);

        let jump_edges = StatefulEdgeBuilder::new().compute_stateful_edges(&graph);
        add_edges(&mut graph, &jump_edges);

        let exit = fix_exit_ecall(&mut graph)?;

        Ok(ControlFlowGraph {
            graph,
            start: NodeIndex::new(0),
            exit,
        })
    }
}

impl fmt::Display for ControlFlowGraph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let dot_graph = Dot::with_config(&self.graph, &[]);

        write!(f, "{:?}", dot_graph)
    }
}

pub type DataSegment = Vec<u8>;

/// Create a `ControlFlowGraph` from an Program without fixing edges
fn create_instruction_graph(program: &Program) -> Result<Graph> {
    ensure!(
        program.code.content.len() % size_of::<u32>() == 0,
        "RISC-U instructions are 32 bits, so the length of the binary must be a multiple of 4"
    );

    let mut g = Graph::new();

    program
        .code
        .content
        .chunks_exact(size_of::<u32>())
        .map(LittleEndian::read_u32)
        .try_for_each(|raw| {
            decode(raw).map(|i| {
                g.add_node(i);
            })
        })
        .context("Failed to decode instructions of program")?;

    Ok(g)
}

/// Compute trivial edges
fn construct_edge_if_trivial(graph: &Graph, idx: NodeIndex) -> Option<Edge> {
    match graph[idx] {
        Instruction::Jal(_) | Instruction::Jalr(_) => None,
        _ if idx.index() + 1 < graph.node_count() => {
            Some((idx, NodeIndex::new(idx.index() + 1), None))
        }
        _ => None,
    }
}

/// Compute pure edges
fn construct_edge_if_pure(graph: &Graph, idx: NodeIndex) -> Option<Edge> {
    match graph[idx] {
        Instruction::Jal(i) if i.rd() == Register::Zero => Some((
            idx,
            NodeIndex::new((((idx.index() as u64) * 4).wrapping_add(i.imm() as u64) / 4) as usize),
            None,
        )),
        Instruction::Beq(i) => Some((
            idx,
            NodeIndex::new((((idx.index() as u64) * 4).wrapping_add(i.imm() as u64) / 4) as usize),
            None,
        )),
        _ => None,
    }
}

/// Compute all edges in `graph`
fn compute_edges<F>(graph: &Graph, f: F) -> Vec<Edge>
where
    F: Fn(&Graph, NodeIndex) -> Option<Edge>,
{
    graph
        .node_indices()
        .filter_map(|idx| f(graph, idx))
        .collect::<Vec<Edge>>()
}

/// Compute all return locations in a given function starting at idx.
fn compute_return_edge_position(graph: &Graph, idx: NodeIndex) -> NodeIndex {
    match graph[idx] {
        Instruction::Jalr(_) => idx,
        Instruction::Jal(i) if i.rd() != Register::Zero => {
            compute_return_edge_position(graph, NodeIndex::new(idx.index() + 1))
        }
        Instruction::Beq(_) => compute_return_edge_position(graph, {
            // second edge is the true branch edge, which jumps to the end of the loop (Selfie
            graph
                .edges(idx)
                .find(|e| e.target().index() != idx.index() + 1)
                .expect("all BEQ edges are constructed already")
                .target()
        }),
        _ => compute_return_edge_position(
            graph,
            graph
                .edges(idx)
                .next()
                .expect("all trivial edges are constructed already")
                .target(),
        ),
    }
}

struct StatefulEdgeBuilder {
    procedure_call_id_seed: u64,
}

impl StatefulEdgeBuilder {
    pub fn new() -> Self {
        Self {
            procedure_call_id_seed: 0,
        }
    }

    /// Calculate stateful edges and return a vector containing them
    pub fn compute_stateful_edges(&mut self, graph: &Graph) -> Vec<Edge> {
        graph
            .node_indices()
            .filter_map(|idx| self.construct_edge_if_stateful(idx, graph))
            .flatten()
            .collect()
    }

    /// Fix stateful edges and return a vector containing them
    fn construct_edge_if_stateful(&mut self, idx: NodeIndex, graph: &Graph) -> Option<Vec<Edge>> {
        match graph[idx] {
            Instruction::Jal(jtype) if jtype.rd() != Register::Zero => {
                // jump and link => function call
                let jump_dest = NodeIndex::new(
                    (((idx.index() as u64) * 4).wrapping_add(jtype.imm() as u64) / 4) as usize,
                );
                let return_dest = NodeIndex::new(idx.index() + 1);
                let id = self.allocate_procedure_call_id();

                let call_edge = (idx, jump_dest, Some(ProcedureCallId::Call(id)));

                let return_edge = (
                    compute_return_edge_position(graph, jump_dest),
                    return_dest,
                    Some(ProcedureCallId::Return(id)),
                );

                Some(vec![call_edge, return_edge])
            }
            _ => None,
        }
    }

    fn allocate_procedure_call_id(&mut self) -> u64 {
        let id = self.procedure_call_id_seed;

        self.procedure_call_id_seed += 1;

        id
    }
}

/// Get exit edge if possible
fn find_possible_exit_edge(graph: &Graph, idx: NodeIndex) -> Option<EdgeIndex> {
    let prev_idx = NodeIndex::new(idx.index() - 1);
    let next_idx = NodeIndex::new(idx.index() + 1);
    match graph[prev_idx] {
        Instruction::Addi(a) => {
            let edge = graph.find_edge(idx, next_idx);
            if a.imm() == 93 {
                edge
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Fix the exit ecall edge
fn fix_exit_ecall(graph: &mut Graph) -> Result<NodeIndex> {
    graph
        .node_indices()
        .find(|idx| {
            if let Instruction::Ecall(_) = graph[*idx] {
                if let Some(edge) = find_possible_exit_edge(graph, *idx) {
                    graph.remove_edge(edge);
                    return true;
                }
            }
            false
        })
        .ok_or_else(|| Error::msg("Could not find exit ecall in binary"))
}

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

use byteorder::{ByteOrder, LittleEndian};
use bytesize::ByteSize;
use log::info;
use petgraph::{
    dot::Dot,
    graph::{EdgeIndex, NodeIndex},
    visit::EdgeRef,
    Graph,
};
use riscu::{decode, load_object_file, Instruction, Program, Register};
use std::{fs::File, io::prelude::*, path::Path, process::Command, vec::Vec};

type Edge = (NodeIndex, NodeIndex, Option<ProcedureCallId>);

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ProcedureCallId {
    Call(u64),
    Return(u64),
}

pub type ControlFlowGraph = Graph<Instruction, Option<ProcedureCallId>>;

static mut PROCEDURE_CALL_ID_SEED: u64 = 0;

fn reset_procedure_call_id_seed() {
    unsafe {
        PROCEDURE_CALL_ID_SEED = 0;
    }
}

fn allocate_procedure_call_id() -> u64 {
    unsafe {
        let id = PROCEDURE_CALL_ID_SEED;
        PROCEDURE_CALL_ID_SEED += 1;
        id
    }
}

/// Create a `ControlFlowGraph` from an `u8` slice without fixing edges
fn create_instruction_graph(binary: &[u8]) -> ControlFlowGraph {
    binary
        .chunks_exact(4)
        .map(LittleEndian::read_u32)
        .map(decode)
        .map(Result::unwrap)
        .fold(ControlFlowGraph::new(), |mut g, i| {
            g.add_node(i);
            g
        })
}

/// Compute trivial edges
fn construct_edge_if_trivial(graph: &ControlFlowGraph, idx: NodeIndex) -> Option<Edge> {
    match graph[idx] {
        Instruction::Jal(_) | Instruction::Jalr(_) => None,
        _ if idx.index() + 1 < graph.node_count() => {
            Some((idx, NodeIndex::new(idx.index() + 1), None))
        }
        _ => None,
    }
}

/// Compute pure edges
fn construct_edge_if_pure(graph: &ControlFlowGraph, idx: NodeIndex) -> Option<Edge> {
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
fn compute_edges<F>(graph: &ControlFlowGraph, f: F) -> Vec<Edge>
where
    F: Fn(&ControlFlowGraph, NodeIndex) -> Option<Edge>,
{
    graph
        .node_indices()
        .filter_map(|idx| f(graph, idx))
        .collect::<Vec<Edge>>()
}

/// Compute all return locations in a given function starting at idx.
fn compute_return_edge_position(graph: &ControlFlowGraph, idx: NodeIndex) -> NodeIndex {
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
                .unwrap()
                .target()
        }),
        _ => compute_return_edge_position(graph, graph.edges(idx).next().unwrap().target()),
    }
}

/// Fix stateful edges and return a vector containing them
fn construct_edge_if_stateful(idx: NodeIndex, graph: &ControlFlowGraph) -> Option<Vec<Edge>> {
    match graph[idx] {
        Instruction::Jal(jtype) if jtype.rd() != Register::Zero => {
            // jump and link => function call
            let jump_dest = NodeIndex::new(
                (((idx.index() as u64) * 4).wrapping_add(jtype.imm() as u64) / 4) as usize,
            );
            let return_dest = NodeIndex::new(idx.index() + 1);
            let id = allocate_procedure_call_id();

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

/// Calculate stateful edges and return a vector containing them
fn compute_stateful_edges(graph: &ControlFlowGraph) -> Vec<Edge> {
    graph
        .node_indices()
        .filter_map(|idx| construct_edge_if_stateful(idx, graph))
        .flatten()
        .collect()
}

/// Get exit edge if possible
fn find_possible_exit_edge(graph: &ControlFlowGraph, idx: NodeIndex) -> Option<EdgeIndex> {
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
fn fix_exit_ecall(graph: &mut ControlFlowGraph) -> NodeIndex {
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
        .unwrap()
}

/// Create a ControlFlowGraph from `u8` slice.
fn build(binary: &[u8]) -> (ControlFlowGraph, NodeIndex) {
    let mut graph = create_instruction_graph(binary);

    fn add_edges(graph: &mut ControlFlowGraph, edges: &[Edge]) {
        edges.iter().for_each(|e| {
            graph.add_edge(e.0, e.1, e.2);
        });
    }

    let edges = compute_edges(&graph, construct_edge_if_trivial);
    add_edges(&mut graph, &edges);

    let pure_edges = compute_edges(&graph, construct_edge_if_pure);
    add_edges(&mut graph, &pure_edges);

    let jump_edges = compute_stateful_edges(&graph);
    add_edges(&mut graph, &jump_edges);

    let exit_node = fix_exit_ecall(&mut graph);

    (graph, exit_node)
}

pub type DataSegment = Vec<u8>;

/// Create a ControlFlowGraph from Path `file`.
// TODO: only tested with Selfie RISC-U file and relies on that ELF format
pub fn build_cfg_from_file<P>(
    file: P,
) -> Result<((ControlFlowGraph, NodeIndex), Program), &'static str>
where
    P: AsRef<Path>,
{
    reset_procedure_call_id_seed();

    let program = load_object_file(file).map_err(|_| "Cannot load RISC-U ELF file")?;

    let cfg = time_info!("generate CFG from binary", {
        build(program.code.content.as_slice())
    });

    Ok((cfg, program))
}

/// Write ControlFlowGraph `graph` to dot file at `file` Path.
pub fn write_to_file<P>(graph: &ControlFlowGraph, file_path: P) -> Result<(), std::io::Error>
where
    P: AsRef<Path>,
{
    let dot_graph = Dot::with_config(graph, &[]);

    let mut file = File::create(file_path.as_ref())?;

    file.write_fmt(format_args!("{:?}", dot_graph))?;
    file.flush()?;

    info!(
        "{} written to file {}",
        ByteSize(file.metadata().unwrap().len()),
        file_path.as_ref().to_str().unwrap(),
    );

    Ok(())
}

/// Convert a dot file into a png file (depends on graphviz)
pub fn convert_dot_to_png(source: &Path, output: &Path) -> Result<(), &'static str> {
    Command::new("dot")
        .arg("-Tpng")
        .arg(source.to_path_buf())
        .arg("-o")
        .arg(output.to_path_buf())
        .output()
        .map_err(|_| "Cannot convert CFG to png file (is graphviz installed?)")?;

    Ok(())
}

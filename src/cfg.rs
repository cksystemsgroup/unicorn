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

use crate::elf::load_file;
use byteorder::{ByteOrder, LittleEndian};
use petgraph::dot::Dot;
use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::Graph;
use riscv_decode::decode;
use riscv_decode::Instruction;
use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::process::Command;
use std::vec::Vec;

type Edge = (NodeIndex, NodeIndex, Option<NodeIndex>);
pub type ControlFlowGraph = Graph<Instruction, Option<NodeIndex>>;

/// Extend sign
pub fn sign_extend(n: u32, b: u32) -> u32 {
    // assert: 0 <= n <= 2^b
    // assert: 0 < b < CPUBITWIDTH
    if n < 2_u32.pow(b - 1) {
        n
    } else {
        n.wrapping_sub(2_u32.pow(b))
    }
}

/// Get `NodeIndex` of `beq` destination.
fn calculate_beq_destination(idx: NodeIndex, imm: u32) -> NodeIndex {
    NodeIndex::new(sign_extend(imm / 4, 11).wrapping_add(idx.index() as u32) as usize)
}

/// Get `NodeIndex` of `jal` destination.
fn calculate_jal_destination(idx: NodeIndex, imm: u32) -> NodeIndex {
    NodeIndex::new(sign_extend(imm / 4, 19).wrapping_add(idx.index() as u32) as usize)
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
        Instruction::Jal(i) if i.rd() == 0 => {
            Some((idx, calculate_jal_destination(idx, i.imm()), None))
        }
        Instruction::Beq(i) => Some((idx, calculate_beq_destination(idx, i.imm()), None)),
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
fn compute_return_edge_position(graph: &ControlFlowGraph, idx: NodeIndex) -> HashSet<NodeIndex> {
    match graph[idx] {
        Instruction::Jalr(_) => {
            let mut set = HashSet::new();
            set.insert(idx);
            set
        }
        Instruction::Jal(i) if i.rd() != 0 => {
            compute_return_edge_position(graph, NodeIndex::new(idx.index() + 1))
        }
        _ => graph
            .edges(idx)
            .flat_map(|e| compute_return_edge_position(graph, e.target()))
            .collect(),
    }
}

/// Fix stateful edges and return a vector containing them
fn construct_edge_if_stateful(idx: NodeIndex, graph: &ControlFlowGraph) -> Option<Vec<Edge>> {
    match graph[idx] {
        Instruction::Jal(jtype) if jtype.rd() != 0 => {
            // jump and link => function call
            let jump_dest = calculate_jal_destination(idx, jtype.imm());
            let return_dest = NodeIndex::new(idx.index() + 1);

            let mut edges = compute_return_edge_position(graph, jump_dest)
                .iter()
                .map(|rp| (*rp, return_dest, Some(idx)))
                .collect::<Vec<Edge>>();

            let call_edge = (idx, jump_dest, Some(idx));

            edges.push(call_edge);

            Some(edges)
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
fn fix_exit_ecall(graph: &mut ControlFlowGraph) {
    graph.node_indices().for_each(|idx| {
        if let Instruction::Ecall = graph[idx] {
            if let Some(edge) = find_possible_exit_edge(graph, idx) {
                graph.remove_edge(edge);
            }
        }
    })
}

/// Create a ControlFlowGraph from `u8` slice.
fn build(binary: &[u8]) -> ControlFlowGraph {
    let mut graph = create_instruction_graph(binary);

    fn add_edges(graph: &mut ControlFlowGraph, edges: Vec<Edge>) {
        edges.iter().for_each(|e| {
            graph.add_edge(e.0, e.1, e.2);
        });
    }

    let edges = compute_edges(&graph, construct_edge_if_trivial);
    add_edges(&mut graph, edges);

    let pure_edges = compute_edges(&graph, construct_edge_if_pure);
    add_edges(&mut graph, pure_edges);

    let jump_edges = compute_stateful_edges(&graph);
    add_edges(&mut graph, jump_edges);

    fix_exit_ecall(&mut graph);

    graph
}

/// Create a ControlFlowGraph from Path `file`.
// TODO: only tested with Selfie RISC-U file and relies on that ELF format
pub fn build_from_file(file: &Path) -> Result<ControlFlowGraph, &str> {
    match load_file(file, 1024) {
        Some((memory_vec, meta_data)) => {
            let memory = memory_vec.as_slice();

            Ok(build(memory.split_at(meta_data.code_length as usize).0))
        }
        None => Err("Cannot load RISC-U ELF file"),
    }
}

/// Write ControlFlowGraph `graph` to dot file at `file` Path.
pub fn write_to_file(graph: &ControlFlowGraph, file: &Path) -> Result<(), std::io::Error> {
    let dot_graph = Dot::with_config(graph, &[]);

    let mut file = File::create(file)?;

    file.write_fmt(format_args!("{:?}", dot_graph))?;

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

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;
    use std::env::current_dir;
    use std::string::String;

    // TODO: write a unit test without dependency on selfie and external files
    #[test]
    #[serial]
    fn can_build_control_flow_graph() {
        let cd = String::from(current_dir().unwrap().to_str().unwrap());

        // generate RISC-U binary with Selfie
        let _ = Command::new("docker")
            .arg("run")
            .arg("-v")
            .arg(cd + ":/opt/monster")
            .arg("cksystemsteaching/selfie")
            .arg("/opt/selfie/selfie")
            .arg("-c")
            .arg("/opt/monster/symbolic/division-by-zero-3-35.c")
            .arg("-o")
            .arg("/opt/monster/symbolic/division-by-zero-3-35.riscu.o")
            .output();

        let test_file = Path::new("symbolic/division-by-zero-3-35.riscu.o");

        let graph = build_from_file(test_file).unwrap();

        let dot_graph = Dot::with_config(&graph, &[]);

        let mut f = File::create("tmp-graph.dot").unwrap();
        f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

        let _ = Command::new("dot")
            .arg("-Tpng")
            .arg("tmp-graph.dot")
            .arg("-o")
            .arg("main.png")
            .output();

        // TODO: test more than just this result
        // assert!(result.is_ok());

        let _ = std::fs::remove_file(test_file);
    }
}

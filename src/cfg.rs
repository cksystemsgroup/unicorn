use crate::elf::load_file;
use byteorder::{ByteOrder, LittleEndian};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Graph;
use riscv_decode::decode;
use riscv_decode::Instruction;
use std::collections::HashSet;
use std::path::Path;
use std::vec::Vec;

type Edge = (NodeIndex, NodeIndex, Option<NodeIndex>);
type ControlFlowGraph = Graph<Instruction, Option<NodeIndex>>;

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

fn construct_edge_if_trivial(graph: &ControlFlowGraph, idx: NodeIndex) -> Option<Edge> {
    match graph[idx] {
        Instruction::Jal(_) | Instruction::Jalr(_) => None,
        Instruction::Beq(i) => {
            // TODO: Handle negative immediate values
            Some((
                idx,
                NodeIndex::new((i.imm() / 4) as usize + idx.index()),
                None,
            ))
        }
        _ if idx.index() + 1 < graph.node_count() => {
            Some((idx, NodeIndex::new(idx.index() + 1), None))
        }
        _ => None,
    }
}

fn compute_trivial_edges(graph: &ControlFlowGraph) -> Vec<Edge> {
    graph
        .node_indices()
        .filter_map(|idx| construct_edge_if_trivial(graph, idx))
        .collect::<Vec<Edge>>()
}

fn sign_extend(n: u32, b: u32) -> u32 {
    // assert: 0 <= n <= 2^b
    // assert: 0 < b < CPUBITWIDTH
    if n < 2_u32.pow(b - 1) {
        n
    } else {
        n.wrapping_sub(2_u32.pow(b))
    }
}

/// Compute all return locations from a function
fn compute_return_edge_position(graph: &ControlFlowGraph, idx: NodeIndex) -> HashSet<NodeIndex> {
    // println!("visit: {:?}", graph[idx]);
    match graph[idx] {
        Instruction::Jalr(_) => {
            let mut set = HashSet::new();
            set.insert(idx);
            set
        }
        Instruction::Jal(_) => compute_return_edge_position(graph, NodeIndex::new(idx.index() + 1)),
        _ => graph
            .edges(idx)
            .flat_map(|e| compute_return_edge_position(graph, e.target()))
            .collect(),
    }
}

fn compute_only_for_jal(idx: NodeIndex, graph: &ControlFlowGraph) -> Option<Vec<Edge>> {
    match graph[idx] {
        Instruction::Jal(jtype) => {
            let imm_signed = sign_extend(jtype.imm() / 4, 19);
            let jump_dest = NodeIndex::new(imm_signed.wrapping_add(idx.index() as u32) as usize);
            let return_dest = NodeIndex::new(idx.index() + 1);

            let mut edges = if jtype.rd() == 0 {
                // jump and drop link
                Vec::<Edge>::new()
            } else {
                // jump and link => function call
                compute_return_edge_position(graph, jump_dest)
                    .iter()
                    .map(|rp| (*rp, return_dest, Some(idx)))
                    .collect::<Vec<Edge>>()
            };

            let call_edge = (idx, jump_dest, Some(idx));

            edges.push(call_edge);

            Some(edges)
        }
        _ => None,
    }
}

fn compute_jal_edges(graph: &ControlFlowGraph) -> Vec<Edge> {
    let indices = graph.node_indices();

    indices
        .filter_map(|idx| compute_only_for_jal(idx, graph))
        .flatten()
        .collect()
}

fn build(binary: &[u8]) -> ControlFlowGraph {
    let mut graph = create_instruction_graph(binary);

    fn add_edges(graph: &mut ControlFlowGraph, edges: Vec<Edge>) {
        edges.iter().for_each(|e| {
            graph.add_edge(e.0, e.1, e.2);
        });
    }

    let edges = compute_trivial_edges(&graph);
    add_edges(&mut graph, edges);

    let jump_edges = compute_jal_edges(&graph);
    add_edges(&mut graph, jump_edges);

    graph
}

// TODO: only tested with Selfie RISC-U file and relies on that ELF format
#[allow(dead_code)]
pub fn build_from_file(file: &Path) -> Result<ControlFlowGraph, &str> {
    match unsafe { load_file(file, 1024) } {
        Some((memory_vec, meta_data)) => {
            let memory = memory_vec.as_slice();

            Ok(build(memory.split_at(meta_data.code_length as usize).0))
        }
        None => todo!("error handling"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::dot::{Config, Dot};
    use serial_test::serial;
    use std::env::current_dir;
    use std::fs::File;
    use std::io::prelude::*;
    use std::process::Command;
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

        let dot_graph = Dot::with_config(&graph, &[Config::EdgeNoLabel]);

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

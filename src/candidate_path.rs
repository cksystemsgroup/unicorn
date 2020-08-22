use crate::cfg::ControlFlowGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use riscv_decode::Instruction;

// extracts a trivial condidate path starting from the very last jump to an ecall (exit)
#[allow(dead_code)]
pub fn extract_trivial_candidate_path(graph: &ControlFlowGraph) -> Vec<Instruction> {
    fn next(graph: &ControlFlowGraph, idx: NodeIndex) -> Option<NodeIndex> {
        let edges = graph.edges_directed(idx, petgraph::Incoming);
        if let Some(edge) = edges.last() {
            Some(edge.source())
        } else {
            None
        }
    }
    let mut path = vec![];
    let mut idx = graph.node_indices().last().unwrap();
    path.push(idx);
    while let Some(n) = next(graph, idx) {
        path.push(n);
        idx = n;
    }
    path.iter().map(|idx| graph[*idx]).collect()
}

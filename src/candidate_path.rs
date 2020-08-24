use crate::cfg::ControlFlowGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use riscv_decode::Instruction;

pub struct CandidatePath<'a> {
    pub root: &'a NodeIndex, // instruction we want to evaluate (exit syscall, division with a potential 0 as divisor, ... )
    pub path: ControlFlowGraph, // instructions which connect the root to the leaves
    pub leaves: Vec<&'a NodeIndex>, // read syscalls
    pub alternative_roots: Vec<&'a NodeIndex>, // alternative roots for generating new candidate paths of the same control-flow graph (relevant for CandidatePath::next())
    pub cfg: &'a ControlFlowGraph, // control-flow graph which this candidate path is extracted from
}

#[allow(dead_code)]
impl<'a> CandidatePath<'a> {
    // may return a reference to a new candidate path using a new root
    pub fn next(&'a mut self) -> &mut CandidatePath {
        self.root = self.alternative_roots.pop().unwrap();
        self.path = ControlFlowGraph::new();
        self.leaves = vec![];

        // self.compute_candidate_path()

        self
    }

    // computes candidate path using its cfg and root fields;
    // populates path and leaves field
    // fn compute_candidate_path(&mut self) -> &mut CandidatePath { }

    // invokes find_roots() which populates the alternative_roots field of the new candidate path
    // invokes compute_candidate_path()
    // pub fn compute_initial_candidate_path(graph: &ControlFlowGraph) -> CandidatePath { }

    // finds root nodes (exit syscall, division with a potential 0 as divisor, ... ) using a provided control-flow graph
    #[allow(dead_code)]
    fn find_roots(graph: &ControlFlowGraph) -> Vec<NodeIndex> {
        let mut roots = vec![];

        graph.node_indices().for_each(|idx| {
            if let Instruction::Ecall = graph[idx] {
                if let Some(idx) = is_exit_point(graph, idx) {
                    roots.push(idx);
                }
            } else if let Instruction::Divu(_rtype) = graph[idx] {
                if let Some(idx) = is_exit_point(graph, idx) {
                    roots.push(idx);
                }
            };
        });

        roots
    }
}

#[allow(dead_code)]
fn is_exit_point(graph: &ControlFlowGraph, idx: NodeIndex) -> Option<NodeIndex> {
    match graph[idx] {
        // get division exit points
        Instruction::Divu(_rtype) => Some(idx),
        _ => match graph[NodeIndex::new(idx.index() - 1)] {
            // get exit syscall exit points
            Instruction::Addi(a) => {
                if a.imm() == 93 {
                    Some(idx)
                } else {
                    None
                }
            }
            _ => None,
        },
    }
}

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

use crate::cfg::ControlFlowGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use riscv_decode::Instruction;

pub struct CandidatePath<'a> {
    pub root: NodeIndex, // instruction we want to evaluate (exit syscall, division with a potential 0 as divisor, ... )
    pub path: ControlFlowGraph, // actual candidate path from the root to instuctions with no incoming edges and read syscalls
    pub alternative_roots: Vec<NodeIndex>, // alternative roots for generating new candidate paths from the same control-flow graph (relevant for CandidatePath::next())
    pub cfg: &'a ControlFlowGraph, // control-flow graph which this candidate path is extracted from
}

#[allow(dead_code)]
impl<'a> CandidatePath<'a> {
    // may return a reference to a candidate path with a new path and root field
    pub fn next(&'a mut self) -> Option<&mut CandidatePath> {
        if let Some(root) = self.alternative_roots.pop() {
            self.root = root;
            self.path = ControlFlowGraph::new();
            self.compute_candidate_path(self.root);
            Some(self)
        } else {
            None
        }
    }

    // computes the candidate path using its cfg and a provided node, it populates its path field;
    // to begin with, this function always gets invoked with a root node as parameter,
    // it adds all "incoming neighbor nodes" (neighbors which are connected with an incoming edge) together with respective incoming edges to the path,
    // then recusively calls itself with those neighboring nodes as parameter,
    // thus propagating through the cfg, continuing to add neighboring nodes and edges
    // the end nodes of the path are read syscalls or nodes with no incoming neighbors
    fn compute_candidate_path(&mut self, node: NodeIndex) {
        self.cfg
            .neighbors_directed(node, petgraph::Incoming)
            .for_each(|x| {
                self.path.node_indices().for_each(|idx| {
                    if self.cfg[x] == self.path[idx] {
                        // node is already in path
                    } else {
                        self.path.add_node(self.cfg[x]);
                    }
                });
                self.path.add_edge(x, node, None);
                match self.cfg[x] {
                    Instruction::Ecall => {
                        if is_read(self.cfg, x) {
                            // stop candidate path generation at read syscalls
                        } else {
                            self.compute_candidate_path(x);
                        }
                    }
                    _ => {
                        self.compute_candidate_path(x);
                    }
                }
            })
    }

    // invokes find_roots() which populates the alternative_roots field of the new candidate path
    // invokes compute_candidate_path() to populate its path field
    pub fn generate_candidate_path(graph: &ControlFlowGraph) -> Option<CandidatePath> {
        // find root nodes (exit syscall, division with a potential 0 as divisor) using a provided control-flow graph
        fn find_roots(graph: &ControlFlowGraph) -> Option<Vec<NodeIndex>> {
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

            if roots.is_empty() {
                None
            } else {
                Some(roots)
            }
        }

        if let Some(mut alternative_roots) = find_roots(&graph) {
            if let Some(root) = alternative_roots.pop() {
                let mut candidate_path = CandidatePath {
                    cfg: graph,
                    path: ControlFlowGraph::new(),
                    root,
                    alternative_roots,
                };
                candidate_path.compute_candidate_path(candidate_path.root);
                Some(candidate_path)
            } else {
                None
            }
        } else {
            None
        }
    }
}

// checks if an instruction is a read syscall
#[allow(dead_code)]
fn is_read(graph: &ControlFlowGraph, idx: NodeIndex) -> bool {
    match graph[NodeIndex::new(idx.index() - 1)] {
        Instruction::Addi(a) => a.imm() == 63,
        _ => false,
    }
}

// checks if an instruction is either a divu or an exit syscall
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

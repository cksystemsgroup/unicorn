use crate::cfg::{ControlFlowGraph, ProcedureCallId};
use itertools::Itertools;
use log::trace;
use petgraph::{
    algo::dijkstra,
    dot::Dot,
    graph::NodeIndex,
    prelude::*,
    visit::{EdgeRef, Reversed},
};
use riscv_decode::{Instruction, Register};
use std::{collections::HashMap, fs::File, io::Write, path::Path};

pub trait ExplorationStrategy {
    fn choose_path(&self, branch1: u64, branch2: u64) -> u64;
}

pub struct ShortestPathStrategy<'a> {
    cfg: &'a ControlFlowGraph,
    distance: HashMap<NodeIndex, u64>,
    entry_address: u64,
}

impl<'a> ShortestPathStrategy<'a> {
    pub fn new(cfg: &'a ControlFlowGraph, entry_address: u64) -> Self {
        time_info!("computing shortest paths in CFG", {
            Self {
                cfg,
                distance: compute_distances(cfg),
                entry_address,
            }
        })
    }

    pub fn write_cfg_with_distances_to_file<P>(&self, path: P) -> Result<(), std::io::Error>
    where
        P: AsRef<Path>,
    {
        let mut f = File::create(path)?;

        write!(f, "{:?}", self)?;

        f.sync_all()?;

        Ok(())
    }

    pub fn distances(&self) -> &HashMap<NodeIndex, u64> {
        &self.distance
    }

    pub fn create_cfg_with_distances(
        &self,
    ) -> Graph<(Instruction, Option<u64>), Option<ProcedureCallId>> {
        self.cfg
            .map(|i, n| (*n, self.distance.get(&i).copied()), |_, e| *e)
    }

    fn address_to_cfg_idx(&self, address: u64) -> NodeIndex {
        NodeIndex::new((address - self.entry_address) as usize / 4)
    }
}

impl<'a> ExplorationStrategy for ShortestPathStrategy<'a> {
    fn choose_path(&self, branch1: u64, branch2: u64) -> u64 {
        let distance1 = self.distance.get(&self.address_to_cfg_idx(branch1));
        let distance2 = self.distance.get(&self.address_to_cfg_idx(branch2));

        trace!("branch distance: d1={:?}, d2={:?}", distance1, distance2);

        match (distance1, distance2) {
            (Some(distance1), Some(distance2)) => {
                if distance1 > distance2 {
                    branch2
                } else {
                    branch1
                }
            }
            (Some(_), None) => branch1,
            (None, Some(_)) => branch2,
            _ => panic!(
                "both branches {} and {} are not reachable!",
                branch1, branch2
            ),
        }
    }
}

pub fn compute_distances(cfg: &ControlFlowGraph) -> HashMap<NodeIndex, u64> {
    let unrolled = time_info!("unrolling CFG", { compute_unrolled_cfg(cfg) });

    let unrolled_reversed = Reversed(&unrolled);

    let exit_node = unrolled
        .node_indices()
        .find(|i| unrolled.edges_directed(*i, Direction::Outgoing).count() == 0)
        .unwrap();

    time_info!("computing distances from exit on unrolled CFG", {
        let distances = dijkstra(unrolled_reversed, exit_node, None, |_| 1_u64);

        let distances_for_idx = unrolled
            .node_indices()
            .filter_map(|i| {
                if let Some(d) = distances.get(&i) {
                    Some((unrolled[i], *d))
                } else {
                    None
                }
            })
            .into_group_map();

        distances_for_idx
            .into_iter()
            .map(|(k, v)| (k, v.into_iter().min().unwrap()))
            .collect::<HashMap<NodeIndex, u64>>()
    })
}

impl std::fmt::Debug for ShortestPathStrategy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cfg_with_distances = self.create_cfg_with_distances();

        let dot_graph = Dot::with_config(&cfg_with_distances, &[]);

        write!(f, "{:?}", dot_graph)
    }
}

pub type UnrolledCfg = Graph<NodeIndex, ()>;

pub fn compute_unrolled_cfg(cfg: &ControlFlowGraph) -> UnrolledCfg {
    Context::new(cfg).compute_unrolled()
}

#[derive(Clone, Copy, Debug)]
enum ExitReason {
    AlreadyVisited,
    ProcedureReturn,
    ExitSyscall,
}

#[derive(Clone)]
pub struct Context<'a> {
    cfg: &'a ControlFlowGraph,
    idx: NodeIndex,
    id: Option<u64>,
    visited: HashMap<NodeIndex, NodeIndex>,
    exit_reason: Option<ExitReason>,
    caller: *const Context<'a>,
}

impl<'a> Context<'a> {
    fn new(cfg: &'a ControlFlowGraph) -> Self {
        Self {
            cfg,
            idx: NodeIndex::new(0),
            id: None,
            visited: HashMap::new(),
            exit_reason: None,
            caller: std::ptr::null(),
        }
    }

    fn compute_unrolled(&mut self) -> UnrolledCfg {
        let mut g = UnrolledCfg::new();

        let n = g.add_node(self.idx);

        self.visited.insert(self.idx, n);

        self.traverse(&mut g);

        g
    }

    fn next(&self) -> NodeIndex {
        self.cfg
            .neighbors_directed(self.idx, Direction::Outgoing)
            .next()
            .unwrap()
    }

    fn visit_unsafe(&mut self, idx: NodeIndex, n: NodeIndex, g: &mut UnrolledCfg) {
        let runtime_location = *self.visited.get(&self.idx).unwrap();

        g.update_edge(runtime_location, n, ());

        trace!(
            "visit: id={:?}, idx={}, instr={:?}",
            self.id,
            idx.index(),
            self.cfg[idx]
        );

        self.visited.insert(idx, n);
        self.idx = idx;
    }

    fn visit(&mut self, idx: NodeIndex, g: &mut UnrolledCfg) {
        let n = self
            .visited
            .get(&idx)
            .copied()
            .unwrap_or_else(|| g.add_node(idx));

        self.visit_unsafe(idx, n, g);
    }

    fn find_call_on_stack(
        &self,
        jal_idx: NodeIndex,
        proc_entry_idx: NodeIndex,
    ) -> Option<NodeIndex> {
        unsafe {
            let mut p: *const Context = self;

            loop {
                if (*p).caller.is_null() {
                    break None;
                } else if (*(*p).caller).idx == jal_idx {
                    if let Some(proc_entry_node) = (*p).visited.get(&proc_entry_idx) {
                        break Some(*proc_entry_node);
                    }
                } else {
                    p = (*p).caller;
                }
            }
        }
    }

    fn traverse(&mut self, g: &mut UnrolledCfg) {
        while self.exit_reason.is_none() {
            match self.cfg[self.idx] {
                Instruction::Jal(jtype) if jtype.rd() != Register::Zero => {
                    let jump_idx = self.next();

                    if let Some(ProcedureCallId::Call(id)) = self
                        .cfg
                        .edges_directed(self.idx, Direction::Outgoing)
                        .next()
                        .unwrap()
                        .weight()
                    {
                        if let Some(proc_entry_node) =
                            self.find_call_on_stack(self.idx, self.next())
                        {
                            self.visit_unsafe(jump_idx, proc_entry_node, g);
                            trace!("jal: (procedure) visited => exiting");

                            self.exit_reason = Some(ExitReason::AlreadyVisited);
                        } else {
                            let mut other = self.clone();
                            trace!("call {:p}: id={}", &other, *id);

                            other.id = Some(*id);
                            other.caller = self;

                            other.visited = HashMap::new();
                            other
                                .visited
                                .insert(other.idx, *self.visited.get(&self.idx).unwrap());
                            other.visit(jump_idx, g);
                            other.traverse(g);

                            trace!("returned from function");

                            match other.exit_reason {
                                Some(ExitReason::ProcedureReturn) => {
                                    self.idx = other.idx;
                                    self.visited
                                        .insert(self.idx, *other.visited.get(&other.idx).unwrap());
                                }
                                Some(_) => {
                                    self.idx = other.idx;
                                    self.exit_reason = other.exit_reason;
                                }
                                _ => unreachable!("reason: {:?}", other.exit_reason),
                            }
                        }
                    } else {
                        panic!("this has to be a procedure call edge")
                    }
                }
                Instruction::Jal(jtype) if jtype.rd() == Register::Zero && jtype.imm() <= 0 => {
                    // end of while loop
                    let jump_idx = self.next();

                    if self.visited.contains_key(&jump_idx) {
                        self.visit(jump_idx, g);
                        trace!("jal: (loop) visited => exiting");
                        self.exit_reason = Some(ExitReason::AlreadyVisited);
                    } else {
                        self.visit(jump_idx, g);
                    }
                }
                Instruction::Jalr(_) => {
                    let mut return_edges = self.cfg.edges_directed(self.idx, Direction::Outgoing);

                    let return_idx = return_edges
                        .find(
                            |e| matches!(e.weight(), Some(ProcedureCallId::Return(id)) if self.id == Some(*id)),
                        )
                        .expect("no matching jalr for jal of type procedure call found")
                        .target();

                    self.visit(return_idx, g);
                    self.exit_reason = Some(ExitReason::ProcedureReturn);

                    trace!("jalr: exiting");
                }
                Instruction::Beq(_) => {
                    let mut neighbors = self.cfg.neighbors_directed(self.idx, Direction::Outgoing);

                    let first = neighbors.next().unwrap();
                    let second = neighbors.next().unwrap();

                    let mut other = self.clone();

                    other.visit(first, g);
                    other.traverse(g);

                    self.visited = other.visited;
                    self.visit(second, g);
                    self.traverse(g);

                    match (other.exit_reason, self.exit_reason) {
                        (Some(ExitReason::ProcedureReturn), _) => {
                            self.idx = other.idx;
                            self.exit_reason = other.exit_reason;
                        }
                        (_, Some(ExitReason::ProcedureReturn)) => {}
                        (Some(ExitReason::ExitSyscall), _) => {
                            self.idx = other.idx;
                            self.exit_reason = other.exit_reason;
                        }

                        (_, Some(ExitReason::ExitSyscall)) => {}
                        (Some(ExitReason::AlreadyVisited), _) => {
                            self.idx = other.idx;
                            self.exit_reason = other.exit_reason;
                        }

                        (_, Some(ExitReason::AlreadyVisited)) => {}
                        _ => panic!("can not return address of return"),
                    };
                }
                Instruction::Ecall(_) => {
                    if self
                        .cfg
                        .edges_directed(self.idx, Direction::Outgoing)
                        .count()
                        == 0
                    {
                        trace!("ecall: (exit) => exiting");
                        self.exit_reason = Some(ExitReason::ExitSyscall);
                    } else {
                        trace!("ecall: (not exit) => go on");
                        self.visit(self.next(), g);
                    }
                }
                _ => self.visit(self.next(), g),
            };
        }
    }
}

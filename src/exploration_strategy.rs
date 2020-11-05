use crate::cfg::{ControlFlowGraph, ProcedureCallId};
use log::trace;
use petgraph::{
    dot::Dot,
    graph::NodeIndex,
    prelude::*,
    visit::{EdgeRef, VisitMap, Visitable},
};
use std::{cmp::Ordering, collections::BinaryHeap};

pub trait ExplorationStrategy {
    fn choose_path(&self, branch1: u64, branch2: u64) -> u64;
}

pub struct ShortestPathStrategy<'a> {
    cfg: &'a ControlFlowGraph,
    distance: Vec<Option<u64>>,
    entry_address: u64,
}

impl<'a> ShortestPathStrategy<'a> {
    pub fn new(cfg: &'a ControlFlowGraph, exit_node: NodeIndex, entry_address: u64) -> Self {
        time_info!("computing shortest paths in CFG", {
            Self {
                cfg,
                distance: dijkstra_with_conditional_edges(cfg, exit_node),
                entry_address,
            }
        })
    }
}

impl<'a> ExplorationStrategy for ShortestPathStrategy<'a> {
    fn choose_path(&self, branch1: u64, branch2: u64) -> u64 {
        let distance1 = self.distance[(branch1 - self.entry_address) as usize / 4];
        let distance2 = self.distance[(branch2 - self.entry_address) as usize / 4];

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

impl std::fmt::Debug for ShortestPathStrategy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let strategy = self.cfg.map(|i, n| (n, self.distance[i.index()]), |_, e| e);

        let dot_graph = Dot::with_config(&strategy, &[]);

        write!(f, "{:?}", dot_graph)
    }
}

/// `MinScored<K, T>` holds a score `K` and a scored object `T` in
/// a pair for use with a `BinaryHeap`.
///
/// `MinScored` compares in reverse order by the score, so that we can
/// use `BinaryHeap` as a min-heap to extract the score-value pair with the
/// least score.
///
/// **Note:** `MinScored` implements a total order (`Ord`), so that it is
/// possible to use float types as scores.
#[derive(Copy, Clone, Debug)]
pub struct MinScored<K, T>(pub K, pub T);

impl<K: PartialOrd, T> PartialEq for MinScored<K, T> {
    #[inline]
    fn eq(&self, other: &MinScored<K, T>) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<K: PartialOrd, T> Eq for MinScored<K, T> {}

impl<K: PartialOrd, T> PartialOrd for MinScored<K, T> {
    #[inline]
    fn partial_cmp(&self, other: &MinScored<K, T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: PartialOrd, T> Ord for MinScored<K, T> {
    #[inline]
    fn cmp(&self, other: &MinScored<K, T>) -> Ordering {
        let a = &self.0;
        let b = &other.0;
        if a == b {
            Ordering::Equal
        } else if a < b {
            Ordering::Greater
        } else if a > b {
            Ordering::Less
        } else if a.ne(a) && b.ne(b) {
            // these are the NaN cases
            Ordering::Equal
        } else if a.ne(a) {
            // Order NaN less, so that it is last in the MinScore order
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

type TraversalState = Vec<ProcedureCallId>;

fn dijkstra_with_conditional_edges(graph: &ControlFlowGraph, start: NodeIndex) -> Vec<Option<u64>> {
    let mut visited = graph.visit_map();

    let zero_score = u64::default();

    let mut scores = graph
        .node_indices()
        .map(|_| None)
        .collect::<Vec<Option<u64>>>();

    let mut visit_next = BinaryHeap::new();

    scores[start.index()] = Some(zero_score);

    visit_next.push(MinScored(zero_score, (start, TraversalState::new())));

    while let Some(MinScored(node_score, (node, ref mut traversal_state))) = visit_next.pop() {
        for edge in graph.edges_directed(node, Direction::Incoming) {
            let next = edge.source();

            let next_score = node_score + 1;

            if visited.is_visited(&next)
                && next_score >= scores[next.index()].unwrap_or(u64::max_value())
            {
                continue;
            }

            match (edge.weight(), traversal_state.last()) {
                // edge without condition
                (None, _) => {}
                (Some(ProcedureCallId::Call(id1)), Some(ProcedureCallId::Return(id2)))
                    if id1 == id2 =>
                {
                    let _ = traversal_state.pop();
                }
                (Some(a @ ProcedureCallId::Return(_)), _) => {
                    traversal_state.push(*a);
                }
                // edge can not be traversed
                a => {
                    trace!("edge can not be traversed:\n  {:?}", a);
                    continue;
                }
            };

            match scores[next.index()] {
                Some(score) => {
                    if next_score < score {
                        visit_next.push(MinScored(next_score, (next, traversal_state.clone())));
                        scores[next.index()] = Some(next_score);
                    }
                }
                None => {
                    visit_next.push(MinScored(next_score, (next, traversal_state.clone())));
                    scores[next.index()] = Some(next_score);
                }
            }
        }
        visited.visit(node);
    }
    scores
}

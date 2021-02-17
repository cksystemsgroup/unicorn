mod control_flow_graph;
mod shortest_path;

pub use self::{control_flow_graph::*, shortest_path::*};

pub trait ExplorationStrategy {
    fn choose_path(&self, branch1: u64, branch2: u64) -> u64;
}

mod coin_flip;
mod control_flow_graph;
mod shortest_path;

pub use self::{coin_flip::*, control_flow_graph::*, shortest_path::*};

use strum::{self, EnumString, EnumVariantNames, IntoStaticStr};

pub trait ExplorationStrategy {
    fn choose_path(&self, branch1: u64, branch2: u64) -> u64;
}

#[derive(Debug, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum ExplorationStrategyType {
    ShortestPaths,
    CoinFlip,
}

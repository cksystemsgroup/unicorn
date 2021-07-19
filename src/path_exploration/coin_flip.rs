use super::ExplorationStrategy;
use rand::{prelude::StdRng, thread_rng, Rng, RngCore, SeedableRng};
use std::cell::RefCell;

pub struct CoinFlipStrategy {
    rng: RefCell<Box<dyn RngCore>>,
}

impl CoinFlipStrategy {
    pub fn new() -> Self {
        Self {
            rng: RefCell::new(Box::new(thread_rng())),
        }
    }

    pub fn from_seed(seed: <StdRng as SeedableRng>::Seed) -> Self {
        Self {
            rng: RefCell::new(Box::new(StdRng::from_seed(seed))),
        }
    }
}

impl Default for CoinFlipStrategy {
    fn default() -> CoinFlipStrategy {
        CoinFlipStrategy::new()
    }
}

impl ExplorationStrategy for CoinFlipStrategy {
    fn choose_path(&self, branch1: u64, branch2: u64) -> u64 {
        if self.rng.borrow_mut().gen::<bool>() {
            branch1
        } else {
            branch2
        }
    }
}

use super::ExplorationStrategy;
use rand::{rngs::ThreadRng, thread_rng, Rng};
use std::cell::RefCell;

pub struct CoinFlipStrategy {
    rng: RefCell<ThreadRng>,
}

impl CoinFlipStrategy {
    pub fn new() -> Self {
        Self {
            rng: RefCell::new(thread_rng()),
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

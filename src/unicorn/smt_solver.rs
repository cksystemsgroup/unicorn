use crate::unicorn::NodeRef;
use std::time::Duration;

//
// Public Interface
//

#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq)]
pub enum SMTSolution {
    Sat,
    Unsat,
    Timeout,
}

// TODO: Clippy in Rust 1.60.0 is overly pedantic. Revisit this on Rust
// upgrades to an even higher version number.
#[allow(clippy::wrong_self_convention)]
pub trait SMTSolver {
    fn new(timeout: Option<Duration>) -> Self;
    fn name() -> &'static str;
    fn solve(&mut self, root: &NodeRef) -> SMTSolution;
    fn is_always_true(&mut self, node: &NodeRef) -> bool;
    fn is_always_false(&mut self, node: &NodeRef) -> bool;
    fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool;
}

//
// Private Implementation
//

// TODO: Move this module into separate file.
pub mod none_impl {
    use crate::unicorn::smt_solver::{SMTSolution, SMTSolver};
    use crate::unicorn::NodeRef;
    use std::time::Duration;

    pub struct NoneSolver {}

    impl SMTSolver for NoneSolver {
        fn name() -> &'static str {
            "None"
        }

        fn new(_timeout: Option<Duration>) -> Self {
            Self {}
        }

        fn is_always_true(&mut self, _node: &NodeRef) -> bool {
            false
        }

        fn is_always_false(&mut self, _node: &NodeRef) -> bool {
            false
        }

        fn is_always_equal(&mut self, _left: &NodeRef, _right: &NodeRef) -> bool {
            false
        }

        fn solve(&mut self, _root: &NodeRef) -> SMTSolution {
            SMTSolution::Timeout
        }
    }
}

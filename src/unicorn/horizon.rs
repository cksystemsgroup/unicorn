use crate::unicorn::{Node, Model};
use crate::cli::{SatType, SmtType};
use crate::unicorn::unroller::{prune_model, renumber_model, unroll_model};
use crate::unicorn::optimize::{
    optimize_model_with_input,
    optimize_model_with_solver,
    optimize_model_with_solver_n
};
use crate::unicorn::smt_solver::*;

use log::{debug, warn};
use std::{
  cmp::min,
  time::{Duration,Instant},
};

//
// Public Interface
//

// pub fn foo(&mut model: Model, &input_values: Vec<u64>, &smt_solver: SmtType, unroll_depth: usize, &time_budget: Option<Duration>, prune: bool, stride: bool) {

// }

//
// Private Interface
//

pub fn print_reasoning_horizon(model: &mut Model) {
    let v: Option<String>;
    v = match &*model.bad_states_initial[0].borrow() {
        Node::Bad { name, ..} => name.clone(),
        _ => None
    };
    
    let bad_state = v.as_ref().expect("Bad state must have an unrolling depth");
    warn!("(Initial) Bad state '{}' is satisfiable.", bad_state);
}

pub fn reason(
    model: &mut Model,
    has_concrete_inputs: bool,
    input_values: &mut Vec<u64>,
    start: usize,
    end: usize,
    prune: bool,
    smt_solver: &SmtType,
    timeout: Option<Duration>,
    minimize: bool
) -> Duration {
    // TODO: Maybe we can get rid of this clone for each
    // iteration, which is basically required if pruning is
    // enabled. However, it is much faster this way than
    // without pruning and not cloning the model.
    let mut model_copy = model.clone();

    let mut now = Instant::now();

    for m in start..end {
        unroll_model(&mut model_copy, m);

        if has_concrete_inputs {
            optimize_model_with_input(&mut model_copy, input_values)
        }
    }

    if prune {
        prune_model(&mut model_copy);
    }

    match smt_solver {
        #[rustfmt::skip]
        SmtType::Generic => {
            optimize_model_with_solver_n::<none_impl::NoneSolver>(&mut model_copy, timeout, minimize)
        },
        #[rustfmt::skip]
        #[cfg(feature = "boolector")]
        SmtType::Boolector => {
            optimize_model_with_solver_n::<boolector_impl::BoolectorSolver>(&mut model_copy, timeout, minimize)
        },
        #[rustfmt::skip]
        #[cfg(feature = "z3")]
        SmtType::Z3 => {
            optimize_model_with_solver_n::<z3solver_impl::Z3SolverWrapper>(&mut model_copy, timeout, minimize)
        },
    }

    now.elapsed()
}

pub fn reason_backwards(
    model: &mut Model,
    has_concrete_inputs: bool,
    input_values: &mut Vec<u64>,
    prev_n: usize,
    n: usize,
    prune: bool,
    smt_solver: &SmtType,
    timeout: Option<Duration>,
    minimize: bool,
    time_budget: &mut Duration,
) -> usize {
    // warn!("Used up time budget of {:#?} somwhere in between the last {} steps", solver_time_budget.map(|&ms| Duration::from_millis(ms)).unwrap(), n-prev_n);
    debug!("Backwards reasoning (binary search) ...");

    let mut start: usize = prev_n;
    let mut end: usize = n;
    let mut last_timeout: usize = n;
    while start <= end {
        let mid: usize = (start + end)/2;

        let elapsed = reason(
            model,
            has_concrete_inputs,
            input_values,
            start,
            mid,
            prune,
            &smt_solver,
            timeout,
            minimize);

        if *time_budget < elapsed {
            end = mid - 1;
            last_timeout = mid;
            debug!("Elapsed: {:#?}", elapsed);
        } else if *time_budget > elapsed
            && last_timeout > mid {
            start = mid + 1;
          
            *time_budget = *time_budget - elapsed;
            debug!("Elapsed: {:#?}", elapsed);
        }

        if *time_budget == elapsed
            || mid + 1 == last_timeout {
            return mid;
        }

        debug!("New steps: {} - {} ...", start, end);
        debug!("Remaining time budget: {:#?} ...", time_budget);
    }
    panic!("No result during backwards reasoning")
}
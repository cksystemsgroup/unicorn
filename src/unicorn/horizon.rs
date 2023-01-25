use crate::unicorn::{Node, NodeRef, Model};
use crate::cli::{SmtType};
use crate::unicorn::unroller::{prune_model, unroll_model};
use crate::unicorn::optimize::{
    optimize_model_with_input,
    optimize_model_with_solver,
    // optimize_model_with_solver_n
};
use crate::unicorn::smt_solver::*;

use log::{debug, warn};
use std::{
    cmp::min,
    time::{Duration,Instant}
};

//
// Public Interface
//

pub fn compute_reasoning_horizon(
    model: &mut Model,
    has_concrete_inputs: bool,
    input_values: &mut Vec<u64>,
    unroll_depth: usize,
    prune: bool,
    stride: bool,
    smt_solver: &SmtType,
    timeout: Option<Duration>,
    minimize: bool,
    terminate_on_bad: bool,
    one_query: bool,
    time_budget: &mut Option<Duration>
) {
    let has_time_budget = !time_budget.is_none();

    let mut n: usize = if stride { 1 } else { unroll_depth };
    let mut prev_n: usize = 0;

    let mut exec_time = Duration::from_millis(0);

    loop {
        // TODO(1): Maybe we can get rid of this clone for each
        // iteration, which is basically required if pruning is
        // enabled. However, it is much faster this way than
        // without pruning and not cloning the model.
        let (elapsed, bad_states_initial) = reason(
            &mut model.clone(),
            has_concrete_inputs,
            input_values,
            prev_n,
            n,
            prune,
            stride,
            &smt_solver,
            timeout,
            minimize,
            terminate_on_bad,
            one_query
        );

        exec_time += elapsed;

        if has_time_budget && time_budget.unwrap() < exec_time {
            exec_time -= elapsed;

            // TODO(2): Cf. TODO(1)
            let r = reason_backwards(
                &mut model.clone(),
                &bad_states_initial,
                prev_n,
                n,
                prune,
                stride,
                &smt_solver,
                timeout,
                minimize,
                terminate_on_bad,
                one_query,
                &(time_budget.unwrap() - exec_time)
            );

            warn!("Reasoning horizon: depth [n={}] (in {:#?}/{:#?})", r.0, exec_time + r.1, time_budget.unwrap());
            break;
        }

        if !stride || !model.bad_states_initial.is_empty() {
            if !model.bad_states_initial.is_empty() {
                print_reasoning_horizon(model);
            }

            break;
        }

        if has_time_budget {
            debug!("Remaining time budget: {:#?} ...", time_budget.unwrap() - exec_time);
        }

        prev_n = n;
        n = min(2*n, unroll_depth);
    }
}

pub fn reason(
    model: &mut Model,
    has_concrete_inputs: bool,
    input_values: &mut Vec<u64>,
    start: usize,
    end: usize,
    prune: bool,
    stride: bool,
    smt_solver: &SmtType,
    timeout: Option<Duration>,
    minimize: bool,
    terminate_on_bad: bool,
    one_query: bool
) -> (Duration, Vec<NodeRef>) {
    let now = Instant::now();

    for m in start..end {
        unroll_model(model, m);

        if has_concrete_inputs {
            optimize_model_with_input(model, input_values)
        }
    }

    if prune {
        prune_model(model);
    }

    let bad_states_initial = model.bad_states_initial.clone();

    match smt_solver {
        #[rustfmt::skip]
        SmtType::Generic => {
            optimize_model_with_solver::<none_impl::NoneSolver>(model, timeout, minimize, terminate_on_bad, one_query, stride)
        },
        #[rustfmt::skip]
        #[cfg(feature = "boolector")]
        SmtType::Boolector => {
            optimize_model_with_solver::<boolector_impl::BoolectorSolver>(model, timeout, minimize, terminate_on_bad, one_query, stride)
        },
        #[rustfmt::skip]
        #[cfg(feature = "z3")]
        SmtType::Z3 => {
            optimize_model_with_solver::<z3solver_impl::Z3SolverWrapper>(model, timeout, minimize, terminate_on_bad, one_query, stride)
        },
    }

    (now.elapsed(), bad_states_initial)
}

//
// Private Interface
//

fn reason_backwards(
  model: &mut Model,
  bad_states_initial: &Vec<NodeRef>,
  prev_n: usize,
  n: usize,
  prune: bool,
  stride: bool,
  smt_solver: &SmtType,
  timeout: Option<Duration>,
  minimize: bool,
  terminate_on_bad: bool,
  one_query: bool,
  time_budget: &Duration,
) -> (usize, Duration) {
  debug!("Backwards reasoning (binary search) for the last {} bad states ...", bad_states_initial.len());

  if prune {
      prune_model(model)
  }

  let mut start: usize = prev_n;
  let mut end: usize = n;
  
  let mut last_n: usize = n;
  let mut last_exec_time = Duration::from_millis(0);

  while start <= end {
      let mid: usize = (start + end)/2;
      let steps: usize = mid - prev_n;

      debug!("Trying to fit remaining time budget {:#?} into the last {} steps ({} to {}) ...", time_budget, steps, prev_n, mid);
      
      let now = Instant::now();

      model.bad_states_initial =
          bad_states_initial.clone()[(prev_n - steps) * 10..].to_vec();

      match smt_solver {
          #[rustfmt::skip]
          SmtType::Generic => {
              optimize_model_with_solver::<none_impl::NoneSolver>(model, timeout, minimize, terminate_on_bad, one_query, stride)
          },
          #[rustfmt::skip]
          #[cfg(feature = "boolector")]
          SmtType::Boolector => {
              optimize_model_with_solver::<boolector_impl::BoolectorSolver>(model, timeout, minimize, terminate_on_bad, one_query, stride)
          },
          #[rustfmt::skip]
          #[cfg(feature = "z3")]
          SmtType::Z3 => {
              optimize_model_with_solver::<z3solver_impl::Z3SolverWrapper>(model, timeout, minimize, terminate_on_bad, one_query, stride)
          },
      }

      let elapsed = now.elapsed();

      if *time_budget < elapsed {
          end = mid - 1;
          debug!("Elapsed time for the last {} steps: {:#?}", steps, elapsed);
      } else if *time_budget > elapsed {
          start = mid + 1;

          last_n = mid;
          last_exec_time = elapsed;
        
          debug!("Elapsed time for the last {} steps: {:#?}", steps, elapsed);
      }
  }

  (last_n, last_exec_time)
}

fn print_reasoning_horizon(model: &mut Model) {
    let v: Option<String>;
    v = match &*model.bad_states_initial[0].borrow() {
        Node::Bad { name, ..} => name.clone(),
        _ => None
    };
    
    let bad_state = v.as_ref().expect("Bad state must have an unrolling depth");
    warn!("(Initial) Bad state '{}' is satisfiable.", bad_state);
}
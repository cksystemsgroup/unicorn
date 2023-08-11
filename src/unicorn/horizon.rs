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
#[cfg(feature = "boolector")]
use crate::unicorn::smt_solver::boolector_impl::BoolectorSolver;
#[cfg(feature = "z3")]
use crate::unicorn::smt_solver::z3solver_impl::Z3SolverWrapper;

//
// Public Interface
//

pub fn compute_bounds<S: SMTSolver>(
    model: &mut Model,
    has_concrete_inputs: bool,
    input_values: &mut Vec<u64>,
    unroll_depth: usize,
    prune: bool,
    smt_solver: &mut S
) {
    let mut prev_depth = 0;
    let mut depth = 1;

    loop {
        for n in prev_depth..depth {
            unroll_model(model, n);
            if has_concrete_inputs {
                optimize_model_with_input(model, input_values)
            }
        }

        let good = &model.good_states_initial[0];
        let n = model.good_states_initial.len();
        let mut lb_found = false;
        let mut lower_bound = 0;
        if !lb_found && (smt_solver.solve(good) == SMTSolution::Sat) {
            lb_found = true;

            let mut l = 0;
            let mut r: isize = (n - 1) as isize;
            let mut m: usize = 0;
            while l <= r {
                m = ((l + r) / 2) as usize;
                if smt_solver.solve(&model.good_states_initial[m]) == SMTSolution::Unsat {
                    r = (m as isize) - 1
                } else {
                    lower_bound = n - m;
                    l = (m as isize) + 1
                }
            }
        }
        if lb_found {
            println!("Exit is reached for some paths: depth n={}", lower_bound);
        } else {
            debug!("Exit is not reached: depth n={}", n);
        }

        let mut ub_found = false;
        let mut upper_bound = 0;
        if smt_solver.is_always_true(good) {
            ub_found = true;

            let mut l = 0;
            let mut r: isize = (n - 1 - lower_bound) as isize;
            let mut m: usize = 0;
            while l <= r {
                m = ((l + r) / 2) as usize;
                if smt_solver.is_always_true(&model.good_states_initial[m]) {
                    upper_bound = n - m;
                    l = (m as isize) + 1
                } else {
                    r = (m as isize) - 1
                }
            }
        }
        if ub_found {
            println!("Exit is reached for all paths: depth n={}", upper_bound);
            break;
        } else {
            debug!("Exit is not reached: depth n={}", n);
        }

        prev_depth = depth;
        depth = min(2*depth, unroll_depth);
    }
}

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

            debug!("Time budget exceeded: {:#?} ({:#?}+{:#?}; elapsed time) / {:#?} (time budget)", exec_time+elapsed, exec_time, elapsed, time_budget.unwrap());

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
                &mut(time_budget.unwrap() - exec_time)
            );

            warn!("Reasoning horizon: depth [n={}] in {:#?} (elapsed time) / {:#?} (time budget)", prev_n + r.0, exec_time + r.1, time_budget.unwrap());
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

    /*let good = &model.good_states_initial[0];
    let mut solver = BoolectorSolver::new(None);
    if solver.solve(good) == SMTSolution::Sat {
        println!("reason: Exit is reached for some paths: len={}", &model.good_states_initial.len());
    }*/

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
  time_budget: &mut Duration,
) -> (usize, Duration) {
  debug!("Backwards reasoning (binary search) for the last {} bad states ...", bad_states_initial.len());

  if prune {
      prune_model(model)
  }

  let mut start: usize = 0;
  let mut end: usize = n - prev_n;
  
  let mut exec_n: usize = end;
  let mut exec_time = Duration::from_millis(0);

  let mut mid: usize = start + (end - start) / 2;
  let mut prev_mid: usize;

  while start < end {
      debug!("Trying to fit remaining time budget {:#?} into the last {} steps ({} to {}) ...", time_budget, mid, mid, end);
      
      let now = Instant::now();

      model.bad_states_initial =
          bad_states_initial.clone()[mid * 10 .. end * 10].to_vec();

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
      
      if *time_budget > elapsed {
        end = mid;
        
        exec_time += elapsed;
          *time_budget -= elapsed;

          debug!("Elapsed time for the last {} steps: {:#?}", mid, elapsed);
      } else if *time_budget < elapsed {
          start = mid;

          exec_n = mid;
          exec_time = elapsed;
        
          debug!("Elapsed time for the last {} steps: {:#?}", mid, elapsed);
      }

      // since we will not find a perfectly fitting time budget (as is the case
      // in a traditional binary search), we need an additional termination
      // criterion to avoid endless loops:
      // We terminate once the pivot does not change anymore.
      prev_mid = mid;
      mid = start + (end - start)/2;

      if prev_mid == mid {
          break;
      }

  }

  (exec_n, exec_time)
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
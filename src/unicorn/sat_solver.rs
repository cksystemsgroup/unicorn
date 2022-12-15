use crate::unicorn::bitblasting::{GateModel, GateRef};
use crate::unicorn::{Node, NodeRef};
use crate::SatType;
use log::{debug, warn};

//
// Public Interface
//

#[allow(unused_variables)]
pub fn solve_bad_states(gate_model: &GateModel, sat_type: SatType) {
    match sat_type {
        SatType::None => unreachable!(),
        #[cfg(feature = "kissat")]
        SatType::Kissat => process_all_bad_states::<kissat_impl::KissatSolver>(gate_model),
    }
}

//
// Private Implementation
//

#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq)]
enum SATSolution {
    Sat,
    Unsat,
    Timeout,
}

trait SATSolver {
    fn new() -> Self;
    fn name() -> &'static str;
    fn decide(&mut self, gate_model: &GateModel, gate: &GateRef) -> SATSolution;
}

fn process_single_bad_state<S: SATSolver>(
    solver: &mut S,
    gate_model: &GateModel,
    bad_state: &NodeRef,
    gate: &GateRef,
) {
    if let Node::Bad { name, .. } = &*bad_state.borrow() {
        let solution = solver.decide(gate_model, gate);
        match solution {
            SATSolution::Sat => {
                warn!(
                    "Bad state '{}' is satisfiable ({})!",
                    name.as_deref().unwrap_or("?"),
                    S::name()
                );
            }
            SATSolution::Unsat => {
                debug!(
                    "Bad state '{}' is unsatisfiable ({}).",
                    name.as_deref().unwrap_or("?"),
                    S::name()
                );
            }
            SATSolution::Timeout => unimplemented!(),
        }
    } else {
        panic!("expecting 'Bad' node here");
    }
}

#[allow(dead_code)]
fn process_all_bad_states<S: SATSolver>(gate_model: &GateModel) {
    debug!("Using {:?} to decide bad states ...", S::name());
    let mut solver = S::new();
    let zip = gate_model
        .bad_state_nodes
        .iter()
        .zip(gate_model.bad_state_gates.iter());
    for (bad_state, gate) in zip {
        process_single_bad_state(&mut solver, gate_model, bad_state, gate)
    }
}

// TODO: Move this module into separate file.
#[cfg(feature = "kissat")]
pub mod kissat_impl {
    use crate::unicorn::bitblasting::{GateModel, GateRef};
    use crate::unicorn::cnf::{CNFBuilder, CNFContainer};
    use crate::unicorn::sat_solver::{SATSolution, SATSolver};
    use kissat_rs::{AnyState, INPUTState, Literal, Solver};

    pub struct KissatSolver {}

    struct KissatContainer {
        current_var: i32,
        solver: Solver,
        state: Option<INPUTState>,
    }

    impl CNFContainer for KissatContainer {
        type Variable = Literal;
        type Literal = Literal;

        fn new() -> Self {
            let (solver, state) = Solver::init();
            Self {
                current_var: 1,
                solver,
                state: Some(state),
            }
        }

        fn name() -> &'static str {
            "Kissat"
        }

        fn var(var: Literal) -> Literal {
            var
        }

        fn neg(var: Literal) -> Literal {
            -var
        }

        fn new_var(&mut self) -> Literal {
            let var = self.current_var;
            self.current_var += 1;
            var
        }

        fn add_clause(&mut self, literals: &[Literal]) {
            let mut state = self.state.take().unwrap();
            state = self.solver.add_clause(literals.to_vec(), state);
            self.state.replace(state);
        }

        fn record_variable_name(&mut self, _var: Literal, _name: String) {
            // nothing to be done here
        }
    }

    impl SATSolver for KissatSolver {
        fn new() -> Self {
            Self {}
        }

        fn name() -> &'static str {
            "Kissat"
        }

        fn decide(&mut self, gate_model: &GateModel, gate: &GateRef) -> SATSolution {
            let mut builder = CNFBuilder::<KissatContainer>::new();

            let bad_state_var = builder.visit(gate);
            builder.container_mut().add_clause(&[bad_state_var]);

            for (gate, val) in &gate_model.constraints {
                let constraint_var = builder.visit(&gate.value);
                let constraint_lit = if *val {
                    KissatContainer::var(constraint_var)
                } else {
                    KissatContainer::neg(constraint_var)
                };
                builder.container_mut().add_clause(&[constraint_lit]);
            }

            let cnf = builder.container_mut();
            let state = cnf.state.take().unwrap();
            match cnf.solver.solve(state).unwrap() {
                AnyState::SAT(..) => SATSolution::Sat,
                AnyState::UNSAT(..) => SATSolution::Unsat,
                AnyState::INPUT(..) => panic!("expecting 'SAT' or 'UNSAT' here"),
            }
        }
    }
}

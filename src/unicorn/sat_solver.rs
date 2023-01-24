use crate::unicorn::bitblasting::{GateModel, GateRef};
use crate::unicorn::{Node, NodeRef};
use anyhow::{anyhow, Result};
use log::{debug, warn};

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
    fn prepare(&mut self, gate_model: &GateModel);
    fn decide(&mut self, gate_model: &GateModel, gate: &GateRef) -> SATSolution;
}

fn process_single_bad_state<S: SATSolver>(
    solver: &mut S,
    gate_model: &GateModel,
    bad_state: &NodeRef,
    gate: &GateRef,
    terminate_on_bad: bool,
) -> Result<()> {
    if let Node::Bad { name, .. } = &*bad_state.borrow() {
        let solution = solver.decide(gate_model, gate);
        match solution {
            SATSolution::Sat => {
                warn!(
                    "Bad state '{}' is satisfiable ({})!",
                    name.as_deref().unwrap_or("?"),
                    S::name()
                );
                if terminate_on_bad {
                    return Err(anyhow!("Bad state satisfiable"));
                }
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
        Ok(())
    } else {
        panic!("expecting 'Bad' node here");
    }
}

#[allow(dead_code)]
fn process_all_bad_states<S: SATSolver>(
    gate_model: &GateModel,
    terminate_on_bad: bool,
) -> Result<()> {
    debug!("Using {:?} to decide bad states ...", S::name());
    let mut solver = S::new();
    let zip = gate_model
        .bad_state_nodes
        .iter()
        .zip(gate_model.bad_state_gates.iter());
    for (bad_state, gate) in zip {
        process_single_bad_state(&mut solver, gate_model, bad_state, gate, terminate_on_bad)?
    }
    Ok(())
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

        fn prepare(&mut self, _gate_model: &GateModel) {
            // nothing to be done here
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

// TODO: Move this module into separate file.
#[cfg(feature = "varisat")]
pub mod varisat_impl {
    use crate::unicorn::bitblasting::{GateModel, GateRef};
    use crate::unicorn::cnf::{CNFBuilder, CNFContainer};
    use crate::unicorn::sat_solver::{SATSolution, SATSolver};
    use varisat_rs::{ExtendFormula, Lit, Solver, Var};

    pub struct VarisatSolver<'a> {
        builder: CNFBuilder<VarisatContainer<'a>>,
    }

    struct VarisatContainer<'a> {
        solver: Solver<'a>,
    }

    impl CNFContainer for VarisatContainer<'_> {
        type Variable = Var;
        type Literal = Lit;

        fn new() -> Self {
            Self {
                solver: Solver::new(),
            }
        }

        fn name() -> &'static str {
            "Varisat"
        }

        fn var(var: Var) -> Lit {
            Lit::positive(var)
        }

        fn neg(var: Var) -> Lit {
            Lit::negative(var)
        }

        fn new_var(&mut self) -> Var {
            self.solver.new_var()
        }

        fn add_clause(&mut self, literals: &[Lit]) {
            self.solver.add_clause(literals)
        }

        fn record_variable_name(&mut self, _var: Var, _name: String) {
            // nothing to be done here
        }
    }

    impl SATSolver for VarisatSolver<'_> {
        fn new() -> Self {
            Self {
                builder: CNFBuilder::<VarisatContainer>::new(),
            }
        }

        fn name() -> &'static str {
            "Varisat"
        }

        fn prepare(&mut self, gate_model: &GateModel) {
            for (gate, val) in &gate_model.constraints {
                let constraint_var = self.builder.visit(&gate.value);
                let constraint_lit = Lit::from_var(constraint_var, *val);
                self.builder.container_mut().add_clause(&[constraint_lit]);
            }
        }

        fn decide(&mut self, _gate_model: &GateModel, gate: &GateRef) -> SATSolution {
            let bad_state_var = self.builder.visit(gate);
            let bad_state_lit = VarisatContainer::var(bad_state_var);
            self.builder.container_mut().solver.assume(&[bad_state_lit]);
            match self.builder.container_mut().solver.solve().unwrap() {
                true => SATSolution::Sat,
                false => SATSolution::Unsat,
            }
        }
    }
}

// TODO: Move this module into separate file.
#[cfg(feature = "cadical")]
pub mod cadical_impl {
    use crate::unicorn::bitblasting::{GateModel, GateRef};
    use crate::unicorn::cnf::{CNFBuilder, CNFContainer};
    use crate::unicorn::sat_solver::{SATSolution, SATSolver};
    use cadical_rs::Solver;

    pub struct CadicalSolver {
        builder: CNFBuilder<CadicalContainer>,
    }

    struct CadicalContainer {
        current_var: i32,
        solver: Solver,
    }

    impl CNFContainer for CadicalContainer {
        type Variable = i32;
        type Literal = i32;

        fn new() -> Self {
            Self {
                current_var: 1,
                solver: Solver::new(),
            }
        }

        fn name() -> &'static str {
            "CaDiCal"
        }

        fn var(var: i32) -> i32 {
            var
        }

        fn neg(var: i32) -> i32 {
            -var
        }

        fn new_var(&mut self) -> i32 {
            let var = self.current_var;
            self.current_var += 1;
            var
        }

        fn add_clause(&mut self, literals: &[i32]) {
            self.solver.add_clause(literals.to_vec())
        }

        fn record_variable_name(&mut self, _var: i32, _name: String) {
            // nothing to be done here
        }
    }

    impl SATSolver for CadicalSolver {
        fn new() -> Self {
            Self {
                builder: CNFBuilder::<CadicalContainer>::new(),
            }
        }

        fn name() -> &'static str {
            "CaDiCal"
        }

        fn prepare(&mut self, gate_model: &GateModel) {
            for (gate, val) in &gate_model.constraints {
                let constraint_var = self.builder.visit(&gate.value);
                let constraint_lit = if *val {
                    CadicalContainer::var(constraint_var)
                } else {
                    CadicalContainer::neg(constraint_var)
                };
                self.builder.container_mut().add_clause(&[constraint_lit]);
            }
        }

        fn decide(&mut self, _gate_model: &GateModel, gate: &GateRef) -> SATSolution {
            let bad_state_var = self.builder.visit(gate);
            let bad_state_lit = CadicalContainer::var(bad_state_var);
            match self
                .builder
                .container_mut()
                .solver
                .solve_with([bad_state_lit].iter().copied())
            {
                Some(true) => SATSolution::Sat,
                Some(false) => SATSolution::Unsat,
                None => SATSolution::Timeout,
            }
        }
    }
}

use crate::unicorn::bitblasting::{get_constant, or_gate, Gate, GateModel, GateRef, Witness};
use crate::unicorn::{Node, NodeRef};
use crate::SatType;
use anyhow::{anyhow, Result};
use log::{debug, trace, warn};
use std::collections::HashMap;
use std::ops::Deref;
use std::panic;
use unicorn::emulate::EmulatorState;

//
// Public Interface
//
#[allow(unused_variables)]
pub fn solve_bad_states(
    gate_model: &GateModel,
    sat_type: SatType,
    terminate_on_bad: bool,
    one_query: bool,
    emulator: EmulatorState,
    extract_witness: bool,
) -> Result<()> {
    match sat_type {
        SatType::None => unreachable!(),
        #[cfg(feature = "kissat")]
        SatType::Kissat => process_all_bad_states::<kissat_impl::KissatSolver>(
            gate_model,
            terminate_on_bad,
            one_query,
            emulator,
            extract_witness,
        ),
        #[cfg(feature = "varisat")]
        SatType::Varisat => process_all_bad_states::<varisat_impl::VarisatSolver>(
            gate_model,
            terminate_on_bad,
            one_query,
            emulator,
            extract_witness,
        ),
        #[cfg(feature = "cadical")]
        SatType::Cadical => process_all_bad_states::<cadical_impl::CadicalSolver>(
            gate_model,
            terminate_on_bad,
            one_query,
            emulator,
            extract_witness,
        ),
    }
}

//
// Private Implementation
//
#[should_panic]
fn emulate_witness(emulator: &mut EmulatorState, witness: Witness) {
    println!(
        "Emulating bad state {:?} with input {:?}:",
        witness.name,
        witness.input_bytes.clone()
    );
    println!("---------------------------------------------------");
    emulator.set_stdin(witness.input_bytes);
    let result = panic::catch_unwind(|| {
        let mut emulator_clone: EmulatorState;
        emulator_clone = emulator.clone();
        emulator_clone.run();
    });
    if result.is_ok() {
        println!("Bad state {} did not produce expected panic.", witness.name);
    }
    println!("---------------------------------------------------\n");
}

#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq)]
enum SATSolution {
    Sat(Option<Witness>),
    Unsat,
    Timeout,
}

trait SATSolver {
    fn new() -> Self;
    fn name() -> &'static str;
    fn prepare(&mut self, gate_model: &GateModel);
    fn decide(&mut self, gate_model: &GateModel, gate: &GateRef) -> SATSolution;

    fn print_witness(witness_ref: &mut Witness) {
        let witness = &witness_ref.gate_assignment;
        let mut input: HashMap<u64, Vec<bool>> = HashMap::new();
        let mut start;
        if witness.is_empty() {
            println!("No witness produced for this bad state.");
            return;
        }

        for key in witness.keys() {
            if let Gate::InputBit { name } = key.value.borrow().deref() {
                // name = "1-byte-input[n=\d][bit=\d]"
                //                        ^--- the 15th char
                // assert: bit is explicit
                start = name.find(']').unwrap();
                let n = name[15..start].parse().unwrap();
                let size = name.chars().next().and_then(|c| c.to_digit(10)).unwrap() as usize;
                let mut bit: usize = name[start + 6..name.len() - 1].parse().unwrap();
                bit = size * 8 - 1 - bit;

                let bit_assignment = *witness.get(key).unwrap();
                if let Some(bits) = input.get_mut(&n) {
                    if let Some(bit_value) = bits.get_mut(bit) {
                        *bit_value = bit_assignment;
                    } else {
                        bits.resize(bit + 1, bit_assignment);
                    }
                } else {
                    let mut bits: Vec<bool> = Vec::new();
                    bits.resize(bit + 1, bit_assignment);
                    input.insert(n, bits);
                }
            } else {
                panic!("Gates in the Witness must be Input Bit Gates.");
            }
        }
        for bits in input {
            let mut output = String::new();
            print!("  input at [n={}] ", bits.0);

            for bit in bits.1 {
                output.push(if bit { '1' } else { '0' });
            }
            let bits_as_int = usize::from_str_radix(&output, 2).unwrap();
            witness_ref.input_bytes.push(bits_as_int);
            println!("{} {}", output, bits_as_int);
        }
    }
}

fn process_single_bad_state<S: SATSolver>(
    solver: &mut S,
    gate_model: &GateModel,
    bad_state_: Option<&NodeRef>,
    gate: &GateRef,
    terminate_on_bad: bool,
    one_query: bool,
    (emulator, extract_witness): (&mut EmulatorState, bool),
) -> Result<()> {
    if !one_query {
        let bad_state = bad_state_.unwrap();
        if let Node::Bad { name, .. } = &*bad_state.borrow() {
            trace!(
                "process_single_bad_state {}",
                name.as_deref().unwrap_or("?")
            );
            let solution = solver.decide(gate_model, gate);
            match solution {
                SATSolution::Sat(witness_opt) => {
                    warn!(
                        "Bad state '{}' is satisfiable ({})!",
                        name.as_deref().unwrap_or("?"),
                        S::name()
                    );
                    if extract_witness {
                        match witness_opt {
                            Some(mut witness) => {
                                witness.name = name.clone().unwrap();
                                println!("Solution by {}: ", S::name());
                                S::print_witness(&mut witness);
                                // TODO: flag for witness emulation
                                emulate_witness(emulator, witness);
                            }
                            None => {
                                println!("No Witness");
                            }
                        }
                    }

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
    } else {
        assert!(bad_state_.is_none());
        let solution = solver.decide(gate_model, gate);
        match solution {
            SATSolution::Sat(..) => {
                warn!("At least one bad state evaluates to true ({})", S::name());
            }
            SATSolution::Unsat => {
                debug!("No bad states occur ({}).", S::name());
            }
            SATSolution::Timeout => unimplemented!(),
        }
        Ok(())
    }
}

#[allow(dead_code)]
fn process_all_bad_states<S: SATSolver>(
    gate_model: &GateModel,
    terminate_on_bad: bool,
    one_query: bool,
    mut emulator: EmulatorState,
    extract_witness: bool,
) -> Result<()> {
    debug!("Using {:?} to decide bad states ...", S::name());
    let mut solver = S::new();

    if !one_query {
        let zip = gate_model
            .bad_state_nodes
            .iter()
            .zip(gate_model.bad_state_gates.iter());

        for (bad_state, gate) in zip {
            process_single_bad_state(
                &mut solver,
                gate_model,
                Some(bad_state),
                gate,
                terminate_on_bad,
                one_query,
                (&mut emulator, extract_witness),
            )?;
        }
    } else {
        let mut ored_bad_states: GateRef;
        if gate_model.bad_state_gates.is_empty() {
            ored_bad_states = GateRef::from(Gate::ConstFalse);
        } else if gate_model.bad_state_gates.len() == 1 {
            ored_bad_states = gate_model.bad_state_gates[0].clone();
        } else {
            let first_element = gate_model.bad_state_gates[0].clone();
            let second_element = gate_model.bad_state_gates[1].clone();
            ored_bad_states = or_gate(
                get_constant(&first_element),
                get_constant(&second_element),
                &first_element,
                &second_element,
            );
        }
        for gate in gate_model.bad_state_gates.iter().skip(2) {
            ored_bad_states = or_gate(
                get_constant(&ored_bad_states),
                get_constant(gate),
                &ored_bad_states,
                gate,
            );
        }
        if let Some(value) = get_constant(&ored_bad_states) {
            if value {
                warn!("Bad state occurs");
            } else {
                warn!("No bad state occurs");
            }
        } else {
            process_single_bad_state(
                &mut solver,
                gate_model,
                None,
                &ored_bad_states,
                terminate_on_bad,
                one_query,
                (&mut emulator, extract_witness),
            )?;
        }
    }

    Ok(())
}

// TODO: Move this module into separate file.
#[cfg(feature = "kissat")]
pub mod kissat_impl {
    use crate::unicorn::bitblasting::{Gate, GateModel, GateRef, HashableGateRef, Witness};
    use crate::unicorn::cnf::{CNFBuilder, CNFContainer};
    use crate::unicorn::sat_solver::{SATSolution, SATSolver};
    use kissat_rs::{AnyState, Assignment, INPUTState, Literal, Solver};
    use std::collections::HashMap;

    pub struct KissatSolver {}

    struct KissatContainer {
        current_var: i32,
        solver: Solver,
        state: Option<INPUTState>,
        variables: HashMap<Literal, GateRef>,
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
                variables: HashMap::new(),
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

        fn record_input(&mut self, var: Self::Variable, gate: &GateRef) {
            if let Gate::InputBit { name } = &*gate.borrow() {
                if name.len() > 1 && name[1..].starts_with("-byte-input") {
                    self.variables.insert(var, gate.clone());
                }
            }
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
            let literals = cnf.variables.keys();

            match cnf.solver.solve(state).unwrap() {
                AnyState::SAT(sat_state) => {
                    let mut witness = Witness {
                        name: String::new(),
                        bad_state_gate: gate.clone(),
                        gate_assignment: HashMap::new(),
                        input_bytes: vec![],
                    };
                    let mut sat = sat_state;
                    for literal in literals.copied() {
                        let value = cnf.solver.value(literal, sat).unwrap();
                        let assignment = match value.0 {
                            Assignment::True => true,
                            Assignment::False => false,
                            Assignment::Both => false,
                        };
                        sat = value.1;
                        let gate_ref = cnf.variables.get(&literal).cloned();
                        witness
                            .gate_assignment
                            .insert(HashableGateRef::from(gate_ref.unwrap()), assignment);
                    }
                    SATSolution::Sat(Some(witness))
                }
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

        #[allow(unused_variables)]
        fn record_input(&mut self, var: Self::Variable, gate: &GateRef) {
            todo!()
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
                true => SATSolution::Sat(None),
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

        #[allow(unused_variables)]
        fn record_input(&mut self, var: Self::Variable, gate: &GateRef) {
            todo!()
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
                Some(true) => SATSolution::Sat(None),
                Some(false) => SATSolution::Unsat,
                None => SATSolution::Timeout,
            }
        }
    }
}

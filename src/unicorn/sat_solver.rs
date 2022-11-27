use crate::unicorn::bitblasting::{Gate, GateModel, GateRef, HashableGateRef};
use crate::unicorn::{Node, NodeRef};
use std::collections::HashMap;

//
// Public Interface
//
pub fn get_sat_formula(gate_model: &GateModel) -> Vec<Vec<i32>> {
    let zip = gate_model
        .bad_state_nodes
        .iter()
        .zip(gate_model.bad_state_gates.iter());
    let mut builder = CNFBuilder::new();
    for (bad_state, gate) in zip {
        builder.convert_bad_state(bad_state, gate);
    }
    for (gate, val) in &gate_model.constraints {
        builder.convert_constraint(&gate.value, *val);
    }
    builder.formula
}

//
// Private Implementation
//
type Variable = i32;

type Clause = Vec<Variable>;
type Formula = Vec<Clause>;

struct CNFBuilder {
    formula: Formula,
    mapping: HashMap<HashableGateRef, Variable>,
    variable_names: Vec<(Variable, String)>,
    final_clause: Clause,
    current_var: Variable,
}

fn var(var: Variable) -> i32 {
    var
}

fn neg(var: Variable) -> i32 {
    -var
}

impl CNFBuilder {
    fn new() -> Self {
        Self {
            formula: Vec::new(),
            mapping: HashMap::new(),
            variable_names: Vec::new(),
            final_clause: Vec::new(),
            current_var: 1,
        }
    }

    fn next_var(&mut self) -> Variable {
        let var = self.current_var;
        self.current_var += 1;
        var
    }

    fn add_clause(&mut self, clause: Clause) {
        self.formula.push(clause);
    }

    fn add_formula(&mut self, formula: Formula) {
        for clause in formula.iter() {
            self.add_clause((*clause).clone());
        }
    }

    fn visit(&mut self, gate: &GateRef) -> (Variable, Formula) {
        let key = HashableGateRef::from(gate.clone());
        let mut formula = vec![];
        let variable = self.mapping.get(&key).copied().unwrap_or_else(|| {
            let (variable_, formula_) = self.process(gate);
            formula = formula_;
            assert!(!self.mapping.contains_key(&key));
            self.mapping.insert(key, variable_);
            variable_
        });
        (variable, formula)
    }

    #[rustfmt::skip]
    fn process(&mut self, gate: &GateRef) -> (Variable, Formula) {
        match &*gate.borrow() {
            Gate::ConstTrue => {
                let gate_var = self.next_var();
                let formula = vec![vec![var(gate_var)]];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::ConstFalse => {
                let gate_var = self.next_var();
                let formula = vec![vec![neg(gate_var)]];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::InputBit { name } => {
                let gate_var = self.next_var();
                self.variable_names.push((gate_var, name.clone()));
                (gate_var, vec![])
            }
            Gate::Not { value } => {
                let (value_var, ..) = self.visit(value);
                let gate_var = self.next_var();
                // Original: X := not(A)
                // Tseytin: (-A | -X) &
                //          (+A | +X)
                let formula = vec![
                    vec![neg(value_var), neg(gate_var)],
                    vec![var(value_var), var(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::And { left, right } => {
                let (left_var, ..) = self.visit(left);
                let (right_var, ..) = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := and(A, B)
                // Tseytin: (-A | -B | +X) &
                //          (+A | -X) &
                //          (+B | -X)
                let formula = vec![
                    vec![neg(left_var), neg(right_var), var(gate_var)],
                    vec![var(left_var), neg(gate_var)],
                    vec![var(right_var), neg(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::Nand { left, right } => {
                let (left_var, ..) = self.visit(left);
                let (right_var, ..) = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := nand(A, B)
                // Tseytin: (-A | -B | -X) &
                //          (+A | +X) &
                //          (+B | +X)
                let formula = vec![
                    vec![neg(left_var), neg(right_var), neg(gate_var)],
                    vec![var(left_var), var(gate_var)],
                    vec![var(right_var), var(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::Or { left, right } => {
                let (left_var, ..) = self.visit(left);
                let (right_var, ..) = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := or(A, B)
                // Tseytin: (+A | +B | -X) &
                //          (-A | +X) &
                //          (-B | +X)
                let formula = vec![
                    vec![var(left_var), var(right_var), neg(gate_var)],
                    vec![neg(left_var), var(gate_var)],
                    vec![neg(right_var), var(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::Matriarch1 { cond, right } => {
                let (cond_var, ..) = self.visit(cond);
                let (right_var, ..) = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := and(not(A), B)
                // Tseytin: (+A | -B | +X) &
                //          (-A | -X) &
                //          (+B | -X)
                let formula = vec![
                    vec![var(cond_var), neg(right_var), var(gate_var)],
                    vec![neg(cond_var), neg(gate_var)],
                    vec![var(right_var), neg(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::CarryHalfAdder { left, right } => {
                let (left_var, ..) = self.visit(left);
                let (right_var, ..) = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := and(A, B)
                // Tseytin: (-A | -B | +X) &
                //          (+A | -X) &
                //          (+B | -X)
                let formula = vec![
                    vec![neg(left_var), neg(right_var), var(gate_var)],
                    vec![var(left_var), neg(gate_var)],
                    vec![var(right_var), neg(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let (input1_var, ..) = self.visit(input1);
                let (input2_var, ..) = self.visit(input2);
                let gate_var = self.next_var();
                // Original: X := xor(A, B)
                // Tseytin: (+A | +B | -X) &
                //          (+A | -B | +X) &
                //          (-A | +B | +X) &
                //          (-A | -B | -X) &
                let formula = vec![
                    vec![var(input1_var), var(input2_var), neg(gate_var)],
                    vec![var(input1_var), neg(input2_var), var(gate_var)],
                    vec![neg(input1_var), var(input2_var), var(gate_var)],
                    vec![neg(input1_var), neg(input2_var), neg(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::CarryFullAdder { input1, input2, input3 } => {
                let (input1_var, ..) = self.visit(input1);
                let (input2_var, ..) = self.visit(input2);
                let (input3_var, ..) = self.visit(input3);
                let gate_var = self.next_var();
                // Original: X := carryFA(A, B, C)
                // Tseytin: (+A | +B | -X) &
                //          (+A | +C | -X) &
                //          (-B | -C | +X) &
                //          (+B | +C | -X) &
                //          (-A | -C | +X) &
                //          (-A | -B | +X)
                let formula = vec![
                    vec![var(input1_var), var(input2_var), neg(gate_var)],
                    vec![var(input1_var), var(input3_var), neg(gate_var)],
                    vec![neg(input2_var), neg(input3_var), var(gate_var)],
                    vec![var(input2_var), var(input3_var), neg(gate_var)],
                    vec![neg(input1_var), neg(input3_var), var(gate_var)],
                    vec![neg(input1_var), neg(input2_var), var(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::ResultFullAdder { input1, input2, input3 } => {
                let (input1_var, ..) = self.visit(input1);
                let (input2_var, ..) = self.visit(input2);
                let (input3_var, ..) = self.visit(input3);
                let gate_var = self.next_var();
                // Original: X := resultFA(A, B, C)
                // Tseytin: (+A | +B | +C | -X) &
                //          (+A | +B | -C | +X) &
                //          (+A | -B | +C | +X) &
                //          (+A | -B | -C | -X) &
                //          (-A | +B | +C | +X) &
                //          (-A | +B | -C | -X) &
                //          (-A | -B | +C | -X) &
                //          (-A | -B | -C | +X) &
                let formula = vec![
                    vec![var(input1_var), var(input2_var), var(input3_var), neg(gate_var)],
                    vec![var(input1_var), var(input2_var), neg(input3_var), var(gate_var)],
                    vec![var(input1_var), neg(input2_var), var(input3_var), var(gate_var)],
                    vec![var(input1_var), neg(input2_var), neg(input3_var), neg(gate_var)],
                    vec![neg(input1_var), var(input2_var), var(input3_var), var(gate_var)],
                    vec![neg(input1_var), var(input2_var), neg(input3_var), neg(gate_var)],
                    vec![neg(input1_var), neg(input2_var), var(input3_var), neg(gate_var)],
                    vec![neg(input1_var), neg(input2_var), neg(input3_var), var(gate_var)]
                ];
                self.add_formula(formula.clone());
                (gate_var, formula)
            }
            Gate::Quotient { name, .. } | Gate::Remainder { name, .. } => {
                let gate_var = self.next_var();
                self.variable_names.push((gate_var, name.clone()));
                (gate_var, vec![])
            }
        }
    }

    fn convert_bad_state(&mut self, bad_state: &NodeRef, gate: &GateRef) {
        let (bad_state_variable, ..) = self.visit(gate);
        if let Node::Bad { name, .. } = &*bad_state.borrow() {
            let name = name.as_deref().unwrap_or("?").to_string();
            self.variable_names.push((bad_state_variable, name));
            self.final_clause.push(var(bad_state_variable));
        } else {
            panic!("expecting 'Bad' node here");
        }
    }

    fn convert_constraint(&mut self, gate: &GateRef, val: bool) {
        let (constraint_variable, ..) = self.visit(gate);
        let constraint_literal = if val {
            var(constraint_variable)
        } else {
            neg(constraint_variable)
        };
        self.add_clause(vec![constraint_literal]);
    }
}

//
// Public Interface
//

#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq)]
pub enum SATSolution {
    Sat,
    Unsat,
    Timeout,
}

// TODO: Clippy in Rust 1.60.0 is overly pedantic. Revisit this on Rust
// upgrades to an even higher version number.
#[allow(clippy::wrong_self_convention)]
pub trait SATSolver {
    fn new(gate_model: &GateModel) -> Self;
    fn name() -> &'static str;
    fn solve(&mut self, gate: &GateRef) -> SATSolution;
    fn is_always_true(&mut self, gate: &GateRef) -> bool;
    fn is_always_false(&mut self, gate: &GateRef) -> bool;
    fn is_always_equal(&mut self, left: &GateRef, right: &GateRef) -> bool;
}

//
// Private Implementation
//

// TODO: Move this module into separate file.
pub mod none_impl {
    use crate::unicorn::sat_solver::{SATSolver, SATSolution};
    use crate::unicorn::bitblasting::{GateRef, GateModel};

    pub struct NoneSATSolver {}

    impl SATSolver for NoneSATSolver {
        fn name() -> &'static str {
            "NoneSAT"
        }

        fn new(_gate_model: &GateModel) -> Self {
            Self {}
        }

        fn is_always_true(&mut self, _gate: &GateRef) -> bool {
            false
        }

        fn is_always_false(&mut self, _gate: &GateRef) -> bool {
            false
        }

        fn is_always_equal(&mut self, _left: &GateRef, _right: &GateRef) -> bool {
            false
        }

        fn solve(&mut self, _gate: &GateRef) -> SATSolution {
            SATSolution::Timeout
        }
    }
}

// TODO: Move this module into separate file.
pub mod kissat_impl {
    use crate::unicorn::sat_solver::{Formula, SATSolution, SATSolver, CNFBuilder,
        Variable, neg, var};
    use crate::unicorn::bitblasting::{GateModel, GateRef};
    use kissat_rs::{Solver, AnyState};

    pub struct KissatSolver {
        builder: CNFBuilder,
    }

    impl SATSolver for KissatSolver {
        fn name() -> &'static str {
            "Kissat"
        }

        fn new(gate_model: &GateModel) -> Self {
            Self {
                builder: process_model(gate_model)
            }
        }

        fn is_always_true(&mut self, gate: &GateRef) -> bool {
            let v = neg(self.visit(gate));
            self.solve_impl(vec![vec![v]]) == SATSolution::Unsat
        }

        fn is_always_false(&mut self, gate: &GateRef) -> bool {
            let v = self.visit(gate);
            self.solve_impl(vec![vec![v]]) == SATSolution::Unsat
        }

        fn is_always_equal(&mut self, left: &GateRef, right: &GateRef) -> bool {
            let v_left = self.visit(left);
            let v_right = self.visit(right);
            let f = vec![
                vec![neg(v_left), var(v_right)],
                vec![var(v_left), neg(v_right)]];
            self.solve_impl(f) == SATSolution::Unsat
        }

        fn solve(&mut self, root: &GateRef) -> SATSolution {
            let v = self.visit(root);
            self.solve_impl(vec![vec![v]])
        }
    }

    fn process_model(gate_model: &GateModel) -> CNFBuilder {
        let zip = gate_model
            .bad_state_nodes
            .iter()
            .zip(gate_model.bad_state_gates.iter());
        let mut builder = CNFBuilder::new();
        for (bad_state, gate) in zip {
            builder.convert_bad_state(bad_state, gate);
        }
        for (gate, val) in &gate_model.constraints {
            builder.convert_constraint(&gate.value, *val);
        }
        builder
    }

    impl KissatSolver {
        fn solve_impl(&mut self, f: Formula) -> SATSolution {
            let (mut solver, mut state) = Solver::init();
            for clause in &self.builder.formula {
                state = solver.add_clause((*clause).clone(), state)
            }
            for clause in f {
                state = solver.add_clause(clause, state)
            }
            let solver_result_state = solver.solve(state).unwrap();
            match solver_result_state {
                AnyState::SAT(..) => SATSolution::Sat,
                AnyState::UNSAT(..) => SATSolution::Unsat,
                AnyState::INPUT(..) => panic!("expecting 'SAT' or 'UNSAT' here"),
            }
        }

        fn visit(&mut self, gate: &GateRef) -> Variable {
            let (variable, ..) = self.builder.visit(gate);
            variable
        }
    }
}

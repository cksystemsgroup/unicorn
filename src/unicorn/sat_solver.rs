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

    fn visit(&mut self, gate: &GateRef) -> Variable {
        let key = HashableGateRef::from(gate.clone());
        self.mapping.get(&key).copied().unwrap_or_else(|| {
            let variable = self.process(gate);
            assert!(!self.mapping.contains_key(&key));
            self.mapping.insert(key, variable);
            variable
        })
    }

    #[rustfmt::skip]
    fn process(&mut self, gate: &GateRef) -> Variable {
        match &*gate.borrow() {
            Gate::ConstTrue => {
                let gate_var = self.next_var();
                self.add_clause(vec![var(gate_var)]);
                gate_var
            }
            Gate::ConstFalse => {
                let gate_var = self.next_var();
                self.add_clause(vec![neg(gate_var)]);
                gate_var
            }
            Gate::InputBit { name } => {
                let gate_var = self.next_var();
                self.variable_names.push((gate_var, name.clone()));
                gate_var
            }
            Gate::Not { value } => {
                let value_var = self.visit(value);
                let gate_var = self.next_var();
                // Original: X := not(A)
                // Tseytin: (-A | -X) &
                //          (+A | +X)
                self.add_clause(vec![neg(value_var), neg(gate_var)]);
                self.add_clause(vec![var(value_var), var(gate_var)]);
                gate_var
            }
            Gate::And { left, right } => {
                let left_var = self.visit(left);
                let right_var = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := and(A, B)
                // Tseytin: (-A | -B | +X) &
                //          (+A | -X) &
                //          (+B | -X)
                self.add_clause(vec![neg(left_var), neg(right_var), var(gate_var)]);
                self.add_clause(vec![var(left_var), neg(gate_var)]);
                self.add_clause(vec![var(right_var), neg(gate_var)]);
                gate_var
            }
            Gate::Nand { left, right } => {
                let left_var = self.visit(left);
                let right_var = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := nand(A, B)
                // Tseytin: (-A | -B | -X) &
                //          (+A | +X) &
                //          (+B | +X)
                self.add_clause(vec![neg(left_var), neg(right_var), neg(gate_var)]);
                self.add_clause(vec![var(left_var), var(gate_var)]);
                self.add_clause(vec![var(right_var), var(gate_var)]);
                gate_var
            }
            Gate::Or { left, right } => {
                let left_var = self.visit(left);
                let right_var = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := or(A, B)
                // Tseytin: (+A | +B | -X) &
                //          (-A | +X) &
                //          (-B | +X)
                self.add_clause(vec![var(left_var), var(right_var), neg(gate_var)]);
                self.add_clause(vec![neg(left_var), var(gate_var)]);
                self.add_clause(vec![neg(right_var), var(gate_var)]);
                gate_var
            }
            Gate::Matriarch1 { cond, right } => {
                let cond_var = self.visit(cond);
                let right_var = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := and(not(A), B)
                // Tseytin: (+A | -B | +X) &
                //          (-A | -X) &
                //          (+B | -X)
                self.add_clause(vec![var(cond_var), neg(right_var), var(gate_var)]);
                self.add_clause(vec![neg(cond_var), neg(gate_var)]);
                self.add_clause(vec![var(right_var), neg(gate_var)]);
                gate_var
            }
            Gate::CarryHalfAdder { left, right } => {
                let left_var = self.visit(left);
                let right_var = self.visit(right);
                let gate_var = self.next_var();
                // Original: X := and(A, B)
                // Tseytin: (-A | -B | +X) &
                //          (+A | -X) &
                //          (+B | -X)
                self.add_clause(vec![neg(left_var), neg(right_var), var(gate_var)]);
                self.add_clause(vec![var(left_var), neg(gate_var)]);
                self.add_clause(vec![var(right_var), neg(gate_var)]);
                gate_var
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let input1_var = self.visit(input1);
                let input2_var = self.visit(input2);
                let gate_var = self.next_var();
                // Original: X := xor(A, B)
                // Tseytin: (+A | +B | -X) &
                //          (+A | -B | +X) &
                //          (-A | +B | +X) &
                //          (-A | -B | -X) &
                self.add_clause(vec![var(input1_var), var(input2_var), neg(gate_var)]);
                self.add_clause(vec![var(input1_var), neg(input2_var), var(gate_var)]);
                self.add_clause(vec![neg(input1_var), var(input2_var), var(gate_var)]);
                self.add_clause(vec![neg(input1_var), neg(input2_var), neg(gate_var)]);
                gate_var
            }
            Gate::CarryFullAdder { input1, input2, input3 } => {
                let input1_var = self.visit(input1);
                let input2_var = self.visit(input2);
                let input3_var = self.visit(input3);
                let gate_var = self.next_var();
                // Original: X := carryFA(A, B, C)
                // Tseytin: (+A | +B | -X) &
                //          (+A | +C | -X) &
                //          (-B | -C | +X) &
                //          (+B | +C | -X) &
                //          (-A | -C | +X) &
                //          (-A | -B | +X)
                self.add_clause(vec![var(input1_var), var(input2_var), neg(gate_var)]);
                self.add_clause(vec![var(input1_var), var(input3_var), neg(gate_var)]);
                self.add_clause(vec![neg(input2_var), neg(input3_var), var(gate_var)]);
                self.add_clause(vec![var(input2_var), var(input3_var), neg(gate_var)]);
                self.add_clause(vec![neg(input1_var), neg(input3_var), var(gate_var)]);
                self.add_clause(vec![neg(input1_var), neg(input2_var), var(gate_var)]);
                gate_var
            }
            Gate::ResultFullAdder { input1, input2, input3 } => {
                let input1_var = self.visit(input1);
                let input2_var = self.visit(input2);
                let input3_var = self.visit(input3);
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
                self.add_clause(vec![var(input1_var), var(input2_var), var(input3_var), neg(gate_var)]);
                self.add_clause(vec![var(input1_var), var(input2_var), neg(input3_var), var(gate_var)]);
                self.add_clause(vec![var(input1_var), neg(input2_var), var(input3_var), var(gate_var)]);
                self.add_clause(vec![var(input1_var), neg(input2_var), neg(input3_var), neg(gate_var)]);
                self.add_clause(vec![neg(input1_var), var(input2_var), var(input3_var), var(gate_var)]);
                self.add_clause(vec![neg(input1_var), var(input2_var), neg(input3_var), neg(gate_var)]);
                self.add_clause(vec![neg(input1_var), neg(input2_var), var(input3_var), neg(gate_var)]);
                self.add_clause(vec![neg(input1_var), neg(input2_var), neg(input3_var), var(gate_var)]);
                gate_var
            }
            Gate::Quotient { name, .. } | Gate::Remainder { name, .. } => {
                let gate_var = self.next_var();
                self.variable_names.push((gate_var, name.clone()));
                gate_var
            }
        }
    }

    fn convert_bad_state(&mut self, bad_state: &NodeRef, gate: &GateRef) {
        let bad_state_variable = self.visit(gate);
        if let Node::Bad { name, .. } = &*bad_state.borrow() {
            let name = name.as_deref().unwrap_or("?").to_string();
            self.variable_names.push((bad_state_variable, name));
            self.final_clause.push(var(bad_state_variable));
        } else {
            panic!("expecting 'Bad' node here");
        }
    }

    fn convert_constraint(&mut self, gate: &GateRef, val: bool) {
        let constraint_variable = self.visit(gate);
        let constraint_literal = if val {
            var(constraint_variable)
        } else {
            neg(constraint_variable)
        };
        self.add_clause(vec![constraint_literal]);
    }
}

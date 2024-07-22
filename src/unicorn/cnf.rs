use crate::unicorn::bitblasting::{Gate, GateRef, HashableGateRef};
use std::collections::HashMap;

//
// Public Interface
//

pub trait CNFContainer {
    type Variable: Copy;
    type Literal;

    fn new() -> Self;
    fn name() -> &'static str;
    fn var(var: Self::Variable) -> Self::Literal;
    fn neg(var: Self::Variable) -> Self::Literal;
    fn new_var(&mut self) -> Self::Variable;
    fn add_clause(&mut self, literals: &[Self::Literal]);
    fn record_variable_name(&mut self, var: Self::Variable, name: String);
    fn record_input(&mut self, var: Self::Variable, gate: &GateRef);
}

pub struct CNFBuilder<C: CNFContainer> {
    mapping: HashMap<HashableGateRef, C::Variable>,
    container: C,
}

impl<C: CNFContainer> CNFBuilder<C> {
    pub fn new() -> Self {
        Self {
            mapping: HashMap::new(),
            container: C::new(),
        }
    }

    pub fn container(&self) -> &C {
        &self.container
    }

    pub fn container_mut(&mut self) -> &mut C {
        &mut self.container
    }

    pub fn visit(&mut self, gate: &GateRef) -> C::Variable {
        let key = HashableGateRef::from(gate.clone());
        self.mapping.get(&key).copied().unwrap_or_else(|| {
            let variable = self.process(gate);
            assert!(!self.mapping.contains_key(&key));
            self.mapping.insert(key, variable);
            variable
        })
    }
}

//
// Private Implementation
//

impl<C: CNFContainer> CNFBuilder<C> {
    fn next_var(&mut self) -> C::Variable {
        self.container.new_var()
    }

    fn add_clause(&mut self, literals: &[C::Literal]) {
        self.container.add_clause(literals);
    }

    fn record_variable_name(&mut self, var: C::Variable, name: String) {
        self.container.record_variable_name(var, name);
    }

    fn record_input(&mut self, var: C::Variable, gate: &GateRef) {
        self.container.record_input(var, gate);
    }

    #[rustfmt::skip]
    fn process(&mut self, gate: &GateRef) -> C::Variable {
        match &*gate.borrow() {
            Gate::ConstTrue => {
                let gate_var = self.next_var();
                self.add_clause(&[C::var(gate_var)]);
                gate_var
            }
            Gate::ConstFalse => {
                let gate_var = self.next_var();
                self.add_clause(&[C::neg(gate_var)]);
                gate_var
            }
            Gate::InputBit { name } => {
                let gate_var = self.next_var();
                self.record_variable_name(gate_var, name.clone());
                self.record_input(gate_var, gate);
                gate_var
            }
            Gate::Not { value } => {
                let value_var = self.visit(value);
                let gate_var = self.next_var();
                // Original: X := not(A)
                // Tseytin: (-A | -X) &
                //          (+A | +X)
                self.add_clause(&[C::neg(value_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(value_var), C::var(gate_var)]);
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
                self.add_clause(&[C::neg(left_var), C::neg(right_var), C::var(gate_var)]);
                self.add_clause(&[C::var(left_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(right_var), C::neg(gate_var)]);
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
                self.add_clause(&[C::neg(left_var), C::neg(right_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(left_var), C::var(gate_var)]);
                self.add_clause(&[C::var(right_var), C::var(gate_var)]);
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
                self.add_clause(&[C::var(left_var), C::var(right_var), C::neg(gate_var)]);
                self.add_clause(&[C::neg(left_var), C::var(gate_var)]);
                self.add_clause(&[C::neg(right_var), C::var(gate_var)]);
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
                self.add_clause(&[C::var(cond_var), C::neg(right_var), C::var(gate_var)]);
                self.add_clause(&[C::neg(cond_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(right_var), C::neg(gate_var)]);
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
                self.add_clause(&[C::neg(left_var), C::neg(right_var), C::var(gate_var)]);
                self.add_clause(&[C::var(left_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(right_var), C::neg(gate_var)]);
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
                self.add_clause(&[C::var(input1_var), C::var(input2_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(input1_var), C::neg(input2_var), C::var(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::var(input2_var), C::var(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::neg(input2_var), C::neg(gate_var)]);
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
                self.add_clause(&[C::var(input1_var), C::var(input2_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(input1_var), C::var(input3_var), C::neg(gate_var)]);
                self.add_clause(&[C::neg(input2_var), C::neg(input3_var), C::var(gate_var)]);
                self.add_clause(&[C::var(input2_var), C::var(input3_var), C::neg(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::neg(input3_var), C::var(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::neg(input2_var), C::var(gate_var)]);
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
                self.add_clause(&[C::var(input1_var), C::var(input2_var), C::var(input3_var), C::neg(gate_var)]);
                self.add_clause(&[C::var(input1_var), C::var(input2_var), C::neg(input3_var), C::var(gate_var)]);
                self.add_clause(&[C::var(input1_var), C::neg(input2_var), C::var(input3_var), C::var(gate_var)]);
                self.add_clause(&[C::var(input1_var), C::neg(input2_var), C::neg(input3_var), C::neg(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::var(input2_var), C::var(input3_var), C::var(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::var(input2_var), C::neg(input3_var), C::neg(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::neg(input2_var), C::var(input3_var), C::neg(gate_var)]);
                self.add_clause(&[C::neg(input1_var), C::neg(input2_var), C::neg(input3_var), C::var(gate_var)]);
                gate_var
            }
            Gate::Quotient { name, .. } | Gate::Remainder { name, .. } => {
                let gate_var = self.next_var();
                self.record_variable_name(gate_var, name.clone());
                gate_var
            }
        }
    }
}

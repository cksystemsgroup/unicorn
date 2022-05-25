use crate::unicorn::bitblasting::{Gate, GateModel, GateRef, HashableGateRef};
use crate::unicorn::get_nid;
use crate::unicorn::HashableNodeRef;
use crate::unicorn::NodeRef;
use anyhow::Result;
use log::info;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::rc::Rc;

pub type QubitRef = Rc<RefCell<Qubit>>;

#[derive(Debug, PartialEq)]
pub struct Qubit {
    pub name: u64,
}

impl From<Qubit> for QubitRef {
    fn from(qubit: Qubit) -> Self {
        Rc::new(RefCell::new(qubit))
    }
}

#[derive(Debug)]
pub struct HashableQubitRef {
    pub value: QubitRef,
}

impl Eq for HashableQubitRef {}

impl PartialEq for HashableQubitRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}

impl From<QubitRef> for HashableQubitRef {
    fn from(qubit: QubitRef) -> Self {
        Self { value: qubit }
    }
}

impl Hash for HashableQubitRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

pub enum Rule {
    Not {
        x1: QubitRef,
    },
    And {
        x1: QubitRef,
        x2: QubitRef,
    },
    Nand {
        x1: QubitRef,
        x2: QubitRef,
    },
    Matriarch1 {
        x1: QubitRef,
        x2: QubitRef,
    },
    Or {
        x1: QubitRef,
        x2: QubitRef,
    },
    AuxHalfAdder {
        x1: QubitRef,
        x2: QubitRef,
    },
    AuxFullAdder {
        x1: QubitRef,
        x2: QubitRef,
        x3: QubitRef,
    },
    CarryHalfAdder {
        x1: QubitRef,
        x2: QubitRef,
    },
    CarryFullAdder {
        x1: QubitRef,
        x2: QubitRef,
        x3: QubitRef,
    },
    ResultHalfAdder {
        x1: QubitRef,
        x2: QubitRef,
    },
    ResultFullAdder {
        x1: QubitRef,
        x2: QubitRef,
        x3: QubitRef,
    },
    Invalid,
    Quotient {
        dividend: Vec<QubitRef>,
        divisor: Vec<QubitRef>,
        index: u32,
    },
    Remainder {
        dividend: Vec<QubitRef>,
        divisor: Vec<QubitRef>,
        index: u32,
    },
}

pub struct Qubo {
    pub linear_coefficients: HashMap<HashableQubitRef, f64>,
    pub quadratic_coefficients: HashMap<HashableQubitRef, HashMap<HashableQubitRef, f64>>,
    pub offset: f64,
    rules: HashMap<HashableQubitRef, Rule>, // used when we want to evaluate an input
    pub fixed_variables: HashMap<HashableQubitRef, bool>, // used for when we want to evaluate an input
    pub is_ising: bool,
}

impl Qubo {
    pub fn new(is_ising: bool) -> Self {
        Self {
            linear_coefficients: HashMap::new(),
            quadratic_coefficients: HashMap::new(),
            offset: 0.0,
            rules: HashMap::new(),
            fixed_variables: HashMap::new(),
            is_ising,
        }
    }

    pub fn binary_to_ising(&mut self) {
        let mut linear_offset = 0.0;
        let mut quadratic_offset = 0.0;

        for value in self.linear_coefficients.values_mut() {
            linear_offset += *value;
            *value *= 0.5;
        }

        for (node, neighbours) in self.quadratic_coefficients.iter_mut() {
            for (neighbour, value) in neighbours.iter_mut() {
                if (*node).value.borrow().name < (*neighbour).value.borrow().name {
                    if let Some(unwrapped_node) = self.linear_coefficients.get_mut(node) {
                        *unwrapped_node += 0.25 * (*value);
                    } else {
                        let key = HashableQubitRef::from((*node).value.clone());
                        self.linear_coefficients.insert(key, 0.25 * (*value));
                    }

                    if let Some(unwrapped_node) = self.linear_coefficients.get_mut(neighbour) {
                        *unwrapped_node += 0.25 * (*value);
                    } else {
                        let key = HashableQubitRef::from((*neighbour).value.clone());
                        self.linear_coefficients.insert(key, 0.25 * (*value));
                    }
                    quadratic_offset += *value;
                }
                *value *= 0.25;
            }
        }
        self.offset += 0.5 * linear_offset + 0.25 * quadratic_offset;
    }

    pub fn get_count_variables(&self) -> usize {
        let set1: HashSet<u64> = self
            .linear_coefficients
            .keys()
            .map(|x| (*x).value.borrow().name)
            .collect();
        let set2: HashSet<u64> = self
            .quadratic_coefficients
            .keys()
            .map(|x| (*x).value.borrow().name)
            .collect();

        set1.union(&set2).count()
    }

    pub fn add_rule(&mut self, qubit: &QubitRef, value: Rule) {
        let key = HashableQubitRef::from(qubit.clone());
        assert!(self.rules.insert(key, value).is_none())
    }

    pub fn add_linear_coeff(&mut self, qubit: &QubitRef, value: f64) {
        if value == 0.0 {
            return;
        }
        let key = HashableQubitRef::from(qubit.clone());
        let entry = self.linear_coefficients.entry(key).or_insert(0.0);
        *entry += value;
    }

    fn add_new_row(&mut self, qubit: &QubitRef) {
        let key = HashableQubitRef::from(qubit.clone());
        self.quadratic_coefficients
            .entry(key)
            .or_insert_with(HashMap::new);
    }

    fn insert_quadratic_coeff(&mut self, qubit1: &QubitRef, qubit2: &QubitRef, value: f64) {
        let key1 = HashableQubitRef::from(qubit1.clone());
        let key2 = HashableQubitRef::from(qubit2.clone());

        let hashmap: &mut HashMap<HashableQubitRef, f64> =
            self.quadratic_coefficients.get_mut(&key1).unwrap();

        if hashmap.contains_key(&key2) {
            let new_coeff = value + hashmap.get(&key2).unwrap();
            hashmap.insert(key2, new_coeff);
        } else {
            hashmap.insert(key2, value);
        }
    }

    pub fn add_quadratic_coeffs(&mut self, qubit1: &QubitRef, qubit2: &QubitRef, value: f64) {
        if value == 0.0 {
            return;
        } else if qubit1.borrow().name == qubit2.borrow().name {
            return self.add_linear_coeff(qubit1, value);
        }

        self.add_new_row(qubit2);
        self.add_new_row(qubit1);

        // trading space for time
        self.insert_quadratic_coeff(qubit1, qubit2, value);
        self.insert_quadratic_coeff(qubit2, qubit1, value);
    }

    pub fn add_offset(&mut self, value: f64) -> f64 {
        self.offset += value;
        self.offset
    }

    pub fn fix_variable(&mut self, qubit: &QubitRef, value: bool) {
        let num: f64 = (value as i64) as f64;

        let key = HashableQubitRef::from(qubit.clone());
        self.fixed_variables.insert(key, value);
        let key = HashableQubitRef::from(qubit.clone());

        assert!(
            self.linear_coefficients.contains_key(&key)
                || self.quadratic_coefficients.contains_key(&key)
        );

        if self.linear_coefficients.contains_key(&key) {
            let coeff = self.linear_coefficients.get(&key).unwrap();
            self.offset += coeff * num;
            self.linear_coefficients.remove(&key);
        }

        if self.quadratic_coefficients.contains_key(&key) {
            let hashmap = <&HashMap<HashableQubitRef, f64>>::clone(
                &self.quadratic_coefficients.get(&key).unwrap(),
            );
            let pairs: Vec<(QubitRef, f64)> =
                hashmap.iter().map(|(x, y)| (x.value.clone(), *y)).collect();
            for (qubit_ref, value) in pairs {
                self.add_linear_coeff(&qubit_ref, value * num);
                let key2 = HashableQubitRef::from(qubit_ref);
                self.quadratic_coefficients
                    .get_mut(&key2)
                    .unwrap()
                    .remove(&key);
            }
            self.quadratic_coefficients.remove(&key);
        }
    }
}

pub struct Qubot<'a> {
    pub qubo: Qubo,
    pub mapping: HashMap<HashableGateRef, QubitRef>,
    mapping_carries: HashMap<HashableGateRef, QubitRef>, // ResultHalfAdder or ResultFullAdder -> to Qubit that represent carries
    const_true_qubit: QubitRef,
    const_false_qubit: QubitRef,
    gate_model: &'a GateModel,
    current_index: u64,
}

impl<'a> Qubot<'a> {
    pub fn new(model: &'a GateModel, is_ising: bool) -> Self {
        Self {
            qubo: Qubo::new(is_ising),
            mapping: HashMap::new(),
            mapping_carries: HashMap::new(),
            const_false_qubit: QubitRef::new(RefCell::new(Qubit { name: 0 })),
            const_true_qubit: QubitRef::new(RefCell::new(Qubit { name: 1 })),
            gate_model: model,
            current_index: 1,
        }
    }

    pub fn get_qubit_value(&self, qubit: &QubitRef) -> Option<bool> {
        let key_qubit = HashableQubitRef::from(qubit.clone());

        if self.qubo.fixed_variables.contains_key(&key_qubit) {
            Some(*self.qubo.fixed_variables.get(&key_qubit).unwrap())
        } else {
            None
        }
    }

    pub fn dump_statistics(&self) {
        let coeffs: Vec<f64> = self.qubo.linear_coefficients.values().cloned().collect();
        info!(
            "linear coefficients   : avg={:.2}, avg_abs={:.2}, min={}, max={}, #={}",
            coeffs.iter().sum::<f64>() / coeffs.len() as f64,
            coeffs.iter().map(|x| f64::abs(*x)).sum::<f64>() / coeffs.len() as f64,
            coeffs.clone().into_iter().reduce(f64::min).unwrap(),
            coeffs.clone().into_iter().reduce(f64::max).unwrap(),
            coeffs.len()
        );

        let mut coeffs: Vec<f64> = Vec::new();
        for (qubit1, edges) in self.qubo.quadratic_coefficients.iter() {
            let id1 = (*qubit1.value.borrow()).name;
            for (qubit2, coeff) in edges.iter() {
                let id2 = (*qubit2.value.borrow()).name;
                if id1 < id2 {
                    coeffs.push(*coeff);
                }
            }
        }
        info!(
            "quadratic coefficients: avg={:.2}, avg_abs={:.2}, min={}, max={}, #={}",
            coeffs.iter().sum::<f64>() / coeffs.len() as f64,
            coeffs.iter().map(|x| f64::abs(*x)).sum::<f64>() as f64 / coeffs.len() as f64,
            coeffs.clone().into_iter().reduce(f64::min).unwrap(),
            coeffs.clone().into_iter().reduce(f64::max).unwrap(),
            coeffs.len()
        );

        let mut connect_map: HashMap<u64, u32> = HashMap::new();
        for (qubit1, edges) in self.qubo.quadratic_coefficients.iter() {
            let id1 = (*qubit1.value.borrow()).name;
            for (qubit2, _) in edges.iter() {
                let id2 = (*qubit2.value.borrow()).name;
                if id1 < id2 {
                    *connect_map.entry(id1).or_insert(0) += 1;
                    *connect_map.entry(id2).or_insert(0) += 1;
                }
            }
        }
        let connect: Vec<u32> = connect_map.values().cloned().collect();
        info!(
            "qubit connectivity    : avg={:.2}, min={}, max={}, #={}",
            connect.iter().sum::<u32>() as f64 / connect.len() as f64,
            connect.iter().min().unwrap(),
            connect.iter().max().unwrap(),
            connect.len()
        );

        info!(
            "number of qubits      : {}",
            self.qubo.get_count_variables()
        );
    }

    pub fn dump_model<W>(&self, mut out: W, bad_state_qubits: Vec<(QubitRef, u64)>) -> Result<()>
    where
        W: Write,
    {
        let num_variables = self.qubo.get_count_variables();
        writeln!(out, "{} {}", num_variables, self.qubo.offset)?;

        writeln!(out)?;

        for (nid, gates) in self.gate_model.input_gates.iter() {
            let mut str_gates: String = "".to_string();
            let mut values: String = "".to_string();
            for gate in gates {
                let gate_key = HashableGateRef::from((*gate).clone());
                let qubit = self.mapping.get(&gate_key).unwrap();
                if !str_gates.is_empty() {
                    values += ",";
                    str_gates += ",";
                }
                str_gates += &(*qubit.borrow()).name.to_string();

                if let Some(qubit_value) = self.get_qubit_value(qubit) {
                    if qubit_value {
                        values += "1";
                    } else {
                        values += "0";
                    }
                } else {
                    values += "-";
                }
            }
            writeln!(out, "{} {} {}", get_nid(nid), str_gates, values)?;
        }

        writeln!(out)?;

        for (qubit, nid) in bad_state_qubits {
            if let Some(qubit_value) = self.get_qubit_value(&qubit) {
                writeln!(
                    out,
                    "{} {} {}",
                    nid,
                    (*qubit.borrow()).name,
                    qubit_value as i32
                )?;
            } else {
                writeln!(out, "{} {}", nid, (*qubit.borrow()).name)?;
            }
        }

        writeln!(out)?;

        // TODO: If Qubits are always referenced by their `name: u64` this can
        // be simplified by just typedef'ing `Qubit` instead.
        let mut sorted_linear_coeffs: Vec<(&HashableQubitRef, &i32)> =
            self.qubo.linear_coefficients.iter().collect();
        sorted_linear_coeffs.sort_by_key(|(qubit, _)| (*qubit.value.borrow()).name);
        for (qubit, coeff) in sorted_linear_coeffs {
            let id = (*qubit.value.borrow()).name;
            writeln!(out, "{} {}", id, *coeff)?;
        }

        writeln!(out)?;
        
        let mut sorted_quadratic_coeffs: Vec<(&HashableQubitRef, &HashMap<HashableQubitRef, i32>)> =
            self.qubo.quadratic_coefficients.iter().collect();
        sorted_quadratic_coeffs.sort_by_key(|(qubit, _)| (*qubit.value.borrow()).name);
        for (qubit1, edges) in sorted_quadratic_coeffs {
            let id1 = (*qubit1.value.borrow()).name;

            let mut sorted_edges: Vec<(&HashableQubitRef, &i32)> = edges.iter().collect();
            sorted_edges.sort_by_key(|(qubit, _)| (*qubit.value.borrow()).name);
            for (qubit2, coeff) in sorted_edges {
                let id2 = (*qubit2.value.borrow()).name;

                if id1 < id2 {
                    writeln!(out, "{} {} {}", id1, id2, *coeff)?;
                }
            }
        }

        Ok(())
    }

    fn get_current_index(&mut self) -> u64 {
        self.current_index += 1;
        self.current_index
    }

    fn update_mapping_carries(&mut self, gate: &GateRef, qubit_carry: QubitRef) {
        let key = HashableGateRef::from(gate.clone());
        assert!(!self.mapping_carries.contains_key(&key));
        self.mapping_carries.insert(key, qubit_carry);
    }

    fn visit(&mut self, gate: &GateRef) -> QubitRef {
        let key = HashableGateRef::from(gate.clone());

        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned().unwrap()
        } else {
            assert!(!self.mapping.contains_key(&key));
            let replacement = self.process_gate(gate);
            assert!(self.mapping.contains_key(&key));

            replacement
        }
    }
    fn record_mapping(&mut self, gate: &GateRef, replacement: QubitRef) -> QubitRef {
        let key = HashableGateRef::from(gate.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement.clone());
        replacement
    }

    pub fn process_gate(&mut self, gate: &GateRef) -> QubitRef {
        match &*gate.borrow() {
            Gate::ConstTrue {} => self.record_mapping(gate, self.const_true_qubit.clone()),
            Gate::ConstFalse {} => self.record_mapping(gate, self.const_false_qubit.clone()),
            Gate::InputBit { name: _ } => {
                let new_qubit = QubitRef::from(RefCell::new(Qubit {
                    name: self.get_current_index(),
                }));
                self.qubo.add_rule(&new_qubit, Rule::Invalid);
                self.record_mapping(gate, new_qubit)
            }
            Gate::Quotient { index, .. } => {
                let new_qubit = QubitRef::from(RefCell::new(Qubit {
                    name: self.get_current_index(),
                }));

                let gate_key = HashableGateRef::from(gate.clone());
                let nodes = self
                    .gate_model
                    .constraint_based_dependencies
                    .get(&gate_key)
                    .unwrap();

                let mut node_key = HashableNodeRef::from(nodes.0.clone());
                let mut temp_gates = self.gate_model.mapping.get(&node_key).unwrap();
                let dividend = temp_gates.iter().map(|g| self.visit(g)).collect();

                node_key = HashableNodeRef::from(nodes.1.clone());
                temp_gates = self.gate_model.mapping.get(&node_key).unwrap();
                let divisor = temp_gates.iter().map(|g| self.visit(g)).collect();

                self.qubo.add_rule(
                    &new_qubit,
                    Rule::Quotient {
                        dividend,
                        divisor,
                        index: *index,
                    },
                );
                self.record_mapping(gate, new_qubit)
            }
            Gate::Remainder { index, .. } => {
                let new_qubit = QubitRef::from(RefCell::new(Qubit {
                    name: self.get_current_index(),
                }));

                let gate_key = HashableGateRef::from(gate.clone());
                let nodes = self
                    .gate_model
                    .constraint_based_dependencies
                    .get(&gate_key)
                    .unwrap();
                let mut dividend: Vec<QubitRef> = Vec::new();

                let mut node_key = HashableNodeRef::from(nodes.0.clone());
                let mut temp_gates = self.gate_model.mapping.get(&node_key).unwrap();
                for t_gate in temp_gates {
                    dividend.push(self.visit(t_gate));
                }

                let mut divisor: Vec<QubitRef> = Vec::new();
                node_key = HashableNodeRef::from(nodes.1.clone());
                temp_gates = self.gate_model.mapping.get(&node_key).unwrap();
                for t_gate in temp_gates {
                    divisor.push(self.visit(t_gate));
                }
                self.qubo.add_rule(
                    &new_qubit,
                    Rule::Remainder {
                        dividend,
                        divisor,
                        index: *index,
                    },
                );
                self.record_mapping(gate, new_qubit)
            }
            Gate::Not { value } => {
                let operand = self.visit(value);
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });

                self.qubo.add_linear_coeff(&operand, -2.0);
                self.qubo.add_linear_coeff(&z, -2.0);

                self.qubo.add_quadratic_coeffs(&operand, &z, 4.0);
                self.qubo.add_offset(2.0);

                self.qubo.add_rule(&z, Rule::Not { x1: operand });
                self.record_mapping(gate, z)
            }
            Gate::And { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });

                self.qubo.add_linear_coeff(&x1, 0.0);
                self.qubo.add_linear_coeff(&x2, 0.0);
                self.qubo.add_linear_coeff(&z, 6.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_offset(0.0);

                self.qubo.add_rule(&z, Rule::And { x1, x2 });
                self.record_mapping(gate, z)
            }
            Gate::Nand { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });

                self.qubo.add_linear_coeff(&x1, -4.0);
                self.qubo.add_linear_coeff(&x2, -4.0);
                self.qubo.add_linear_coeff(&z, -6.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, 4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, 4.0);

                self.qubo.add_offset(6.0);

                self.qubo.add_rule(&z, Rule::Nand { x1, x2 });
                self.record_mapping(gate, z)
            }
            Gate::Matriarch1 { cond, right } => {
                let x1 = self.visit(cond);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });

                self.qubo.add_linear_coeff(&x1, 0.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, -2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, 4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_offset(0.0);

                self.qubo.add_rule(&z, Rule::Matriarch1 { x1, x2 });
                self.record_mapping(gate, z)
            }
            Gate::Or { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });

                self.qubo.add_linear_coeff(&x1, 2.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_offset(0.0);

                self.qubo.add_rule(&z, Rule::Or { x1, x2 });
                self.record_mapping(gate, z)
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let x1 = self.visit(input1);
                let x2 = self.visit(input2);

                let aux = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });
                let carry = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });

                self.update_mapping_carries(gate, carry.clone());

                self.qubo.add_linear_coeff(&x1, 2.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);
                self.qubo.add_linear_coeff(&aux, 4.0);
                self.qubo.add_linear_coeff(&carry, 4.0);

                self.qubo.add_quadratic_coeffs(&carry, &aux, 4.0);
                self.qubo.add_quadratic_coeffs(&x1, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &aux, 4.0);
                self.qubo.add_quadratic_coeffs(&x2, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &x2, 0.0);
                self.qubo.add_quadratic_coeffs(&z, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&z, &carry, 4.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, 0.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_rule(
                    &carry,
                    Rule::CarryHalfAdder {
                        x1: x1.clone(),
                        x2: x2.clone(),
                    },
                );
                self.qubo.add_rule(
                    &aux,
                    Rule::AuxHalfAdder {
                        x1: x1.clone(),
                        x2: x2.clone(),
                    },
                );
                self.qubo.add_rule(&z, Rule::ResultHalfAdder { x1, x2 });
                self.record_mapping(gate, z)
            }
            Gate::ResultFullAdder {
                input1,
                input2,
                input3,
            } => {
                let x1 = self.visit(input1);
                let x2 = self.visit(input2);
                let x3 = self.visit(input3);

                let aux = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });
                let carry = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });

                self.update_mapping_carries(gate, carry.clone());

                self.qubo.add_linear_coeff(&x1, 2.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&x3, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);
                self.qubo.add_linear_coeff(&aux, 4.0);
                self.qubo.add_linear_coeff(&carry, 4.0);

                self.qubo.add_quadratic_coeffs(&x1, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &x2, 4.0);
                self.qubo.add_quadratic_coeffs(&x3, &aux, 4.0);
                self.qubo.add_quadratic_coeffs(&x3, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&z, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&z, &carry, 4.0);
                self.qubo.add_quadratic_coeffs(&z, &x3, -4.0);

                self.qubo.add_rule(
                    &carry,
                    Rule::CarryFullAdder {
                        x1: x1.clone(),
                        x2: x2.clone(),
                        x3: x3.clone(),
                    },
                );
                self.qubo.add_rule(
                    &aux,
                    Rule::AuxFullAdder {
                        x1: x1.clone(),
                        x2: x2.clone(),
                        x3: x3.clone(),
                    },
                );
                self.qubo.add_rule(&z, Rule::ResultFullAdder { x1, x2, x3 });
                self.qubo.add_offset(0.0);
                self.record_mapping(gate, z)
            }
            Gate::CarryHalfAdder { .. } => {
                let key = HashableGateRef::from(gate.clone());
                let gate_half_adder = self.gate_model.mapping_adders.get(&key).unwrap();
                self.visit(gate_half_adder);

                let half_adder_key = HashableGateRef::from(gate_half_adder.clone());
                let z = (*self.mapping_carries.get(&half_adder_key).unwrap()).clone();
                self.record_mapping(gate, z)
            }
            Gate::CarryFullAdder { .. } => {
                let key = HashableGateRef::from(gate.clone());
                let gate_full_adder = self.gate_model.mapping_adders.get(&key).unwrap();
                self.visit(gate_full_adder);

                let full_adder_key = HashableGateRef::from(gate_full_adder.clone());
                let z = (*self.mapping_carries.get(&full_adder_key).unwrap()).clone();
                self.record_mapping(gate, z)
            }
        }
    }

    pub fn build_qubo(&mut self) -> Vec<(QubitRef, u64)> {
        let mut bad_state_qubits: Vec<(QubitRef, u64)> = Vec::new();
        let bad_states_zipped = self
            .gate_model
            .bad_state_nodes
            .iter()
            .zip(self.gate_model.bad_state_gates.iter());
        for (node, gate) in bad_states_zipped {
            let qubit = self.process_gate(gate);
            let key_qubit = HashableQubitRef::from(qubit.clone());
            if !self.qubo.fixed_variables.contains_key(&key_qubit) {
                // only add qubits that does not have a fixed value
                bad_state_qubits.push((qubit, get_nid(node)));
            }
        }

        // or bad states
        if !bad_state_qubits.is_empty() {
            let mut ored_bad_states = bad_state_qubits[0].0.clone();

            for (qubit, _) in bad_state_qubits.iter().skip(1) {
                // or bad state
                let z = QubitRef::from(Qubit {
                    name: self.get_current_index(),
                });
                self.qubo.add_linear_coeff(&ored_bad_states, 2.0);
                self.qubo.add_linear_coeff(qubit, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);

                self.qubo.add_rule(
                    &z,
                    Rule::Or {
                        x1: ored_bad_states.clone(),
                        x2: qubit.clone(),
                    },
                );

                self.qubo.add_quadratic_coeffs(&ored_bad_states, qubit, 2.0);
                self.qubo.add_quadratic_coeffs(&ored_bad_states, &z, -4.0);
                self.qubo.add_quadratic_coeffs(qubit, &z, -4.0);
                ored_bad_states = z;
            }

            // fix ored bad states to be true
            self.qubo.fix_variable(&ored_bad_states, true);
        } else {
            panic!("No bad states qubits!");
        }

        // apply constraints
        for (gate, value) in self.gate_model.constraints.iter() {
            let qubit = self.mapping.get(gate).unwrap();
            self.qubo.fix_variable(qubit, *value);
        }

        // fix true constants
        self.qubo.fix_variable(&self.const_true_qubit, true);

        //fix false constants
        self.qubo.fix_variable(&self.const_false_qubit, false);

        if self.qubo.is_ising {
            self.qubo.binary_to_ising();
        }

        bad_state_qubits
    }
}

pub struct InputEvaluator {
    pub fixed_qubits: HashMap<HashableQubitRef, bool>,
}

impl InputEvaluator {
    pub fn new() -> Self {
        Self {
            fixed_qubits: HashMap::new(),
        }
    }

    fn get_numeric_value(&mut self, qubits: &[QubitRef], qubo: &Qubo) -> u64 {
        let mut result = 0;
        let mut current_power = 1;
        for qubit in qubits {
            if self.get_qubit_value(qubit, qubo) {
                result += current_power;
            }
            current_power *= 2;
        }
        result
    }

    fn get_qubit_value(&mut self, z: &QubitRef, qubo: &Qubo) -> bool {
        let key = HashableQubitRef::from(z.clone());
        if let Some(value) = self.fixed_qubits.get(&key) {
            return *value;
        } else if let Some(value) = qubo.fixed_variables.get(&key) {
            return *value;
        }
        let current_rule = qubo.rules.get(&key).unwrap();
        match current_rule {
            Rule::Not { x1 } => {
                let value_x1 = self.get_qubit_value(x1, qubo);
                self.fixed_qubits.insert(key, !value_x1);
                !value_x1
            }
            Rule::Quotient {
                dividend,
                divisor,
                index,
            }
            | Rule::Remainder {
                dividend,
                divisor,
                index,
            } => {
                let dividend_value = self.get_numeric_value(dividend, qubo);
                let divisor_value = self.get_numeric_value(divisor, qubo);

                let mut result: u64;

                match current_rule {
                    Rule::Quotient { .. } => {
                        result = dividend_value / divisor_value;
                    }
                    Rule::Remainder { .. } => {
                        result = dividend_value % divisor_value;
                    }
                    _ => {
                        panic!("[RULE DIVISION/REMAINDER]this should not happen!");
                    }
                }

                for _ in 0..*index {
                    result /= 2
                }
                result % 2 == 1
            }
            Rule::And { x1, x2 }
            | Rule::Nand { x1, x2 }
            | Rule::Matriarch1 { x1, x2 }
            | Rule::Or { x1, x2 }
            | Rule::AuxHalfAdder { x1, x2 }
            | Rule::CarryHalfAdder { x1, x2 }
            | Rule::ResultHalfAdder { x1, x2 } => {
                let value_x1 = self.get_qubit_value(x1, qubo);
                let value_x2 = self.get_qubit_value(x2, qubo);
                match current_rule {
                    Rule::And { .. } | Rule::CarryHalfAdder { .. } => {
                        self.fixed_qubits.insert(key, value_x1 && value_x2);
                        value_x1 && value_x2
                    }
                    Rule::Nand { .. } => {
                        self.fixed_qubits.insert(key, !(value_x1 && value_x2));
                        !(value_x1 && value_x2)
                    }
                    Rule::Matriarch1 { .. } => {
                        self.fixed_qubits.insert(key, !value_x1 && value_x2);
                        !value_x1 && value_x2
                    }
                    Rule::Or { .. } => {
                        self.fixed_qubits.insert(key, value_x1 || value_x2);
                        value_x1 || value_x2
                    }
                    Rule::AuxHalfAdder { .. } => {
                        self.fixed_qubits.insert(key, value_x1 && !value_x2);
                        value_x1 && !value_x2
                    }
                    Rule::ResultHalfAdder { .. } => {
                        self.fixed_qubits.insert(key, value_x1 != value_x2);
                        value_x1 != value_x2
                    }
                    _ => {
                        panic!("this rule should not happen!");
                    }
                }
            }
            Rule::AuxFullAdder { x1, x2, x3 }
            | Rule::CarryFullAdder { x1, x2, x3 }
            | Rule::ResultFullAdder { x1, x2, x3 } => {
                let value_x1 = self.get_qubit_value(x1, qubo);
                let value_x2 = self.get_qubit_value(x2, qubo);
                let value_x3 = self.get_qubit_value(x3, qubo);

                match current_rule {
                    Rule::AuxFullAdder { .. } => {
                        let aux: bool;
                        if !value_x1 {
                            if !value_x2 {
                                aux = false;
                            } else if !value_x3 {
                                aux = true;
                            } else {
                                aux = false;
                            }
                        } else if value_x2 {
                            aux = true;
                        } else if value_x3 {
                            aux = false;
                        } else {
                            aux = true;
                        }

                        self.fixed_qubits.insert(key, aux);
                        aux
                    }
                    Rule::CarryFullAdder { .. } => {
                        let result = (value_x1 as i32) + (value_x2 as i32) + (value_x3 as i32) > 1;
                        self.fixed_qubits.insert(key, result);
                        result
                    }
                    Rule::ResultFullAdder { .. } => {
                        let result =
                            (((value_x1 as i32) + (value_x2 as i32) + (value_x3 as i32)) % 2) == 1;
                        self.fixed_qubits.insert(key, result);
                        result
                    }
                    _ => {
                        panic!("This rule should not be happening!");
                    }
                }
            }
            Rule::Invalid => {
                panic!("[Input Evaluator] There is a dependency that cannot be resolved.")
            }
        }
    }

    pub fn evaluate_inputs(
        &mut self,
        qubo: &Qubo,
        mapping: &HashMap<HashableGateRef, QubitRef>,
        input_gates: &[(NodeRef, Vec<GateRef>)],
        input_values: &[i64],
        bad_states: Vec<(QubitRef, u64)>,
    ) -> (f64, Vec<u64>) {
        assert!(input_gates.len() == input_values.len());

        // fix qubits that represent input
        for (gates, value) in input_gates.iter().zip(input_values.iter()) {
            let mut current_val = *value;
            let gates: Vec<GateRef> = gates.1.to_vec();
            for gate in gates {
                let gate_key = HashableGateRef::from(gate);
                let qubit_ref = &*(mapping.get(&gate_key).unwrap());
                let qubit_key = HashableQubitRef::from(qubit_ref.clone());
                self.fixed_qubits.insert(qubit_key, (current_val % 2) == 1);
                current_val /= 2;
            }
        }

        // start solving QUBO
        let mut offset = qubo.offset;

        for (qubit_hash, coeff) in qubo.linear_coefficients.iter() {
            let qubit_value = self.get_qubit_value(&qubit_hash.value, qubo);
            let final_value: f64;
            if qubo.is_ising && !qubit_value {
                final_value = -1.0;
            } else {
                final_value = (qubit_value as u64) as f64;
            }
            offset += (*coeff) * final_value;
        }

        for (qubit_hash1, more_qubits) in qubo.quadratic_coefficients.iter() {
            let mut value1 = (self.get_qubit_value(&qubit_hash1.value, qubo) as i64) as f64;
            if qubo.is_ising && value1 == 0.0 {
                value1 = -1.0;
            }
            for (qubit_hash2, coeff) in more_qubits.iter() {
                if qubit_hash1.value.borrow().name < qubit_hash2.value.borrow().name {
                    let mut value2 = (self.get_qubit_value(&qubit_hash2.value, qubo) as i64) as f64;

                    if qubo.is_ising && value2 == 0.0 {
                        value2 = -1.0;
                    }
                    offset += value1 * value2 * coeff;
                }
            }
        }

        let mut true_bad_states = vec![];
        // which bad states happen? :
        for (qubit, nid) in bad_states {
            let value = self.get_qubit_value(&qubit, qubo);
            if value {
                true_bad_states.push(nid);
            }
        }

        (offset, true_bad_states)
    }
}

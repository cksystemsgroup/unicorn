use crate::unicorn::{get_nid, HashableNodeRef, Model, Nid, Node, NodeRef, NodeType};
use anyhow::Result;
use std::cell::RefCell;
use std::cmp::max;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::rc::Rc;

//
// Public Interface
//

// TODO: MAYBE CX gates are not needed. (We can just push the control qubit to the result)
// BEGIN structs declaration
pub type UnitaryRef = Rc<RefCell<Unitary>>;

#[derive(Debug)]
pub enum Unitary {
    Not {
        input: QubitRef,
    },
    Cnot {
        control: QubitRef,
        target: QubitRef,
    },
    Mcx {
        controls: Vec<QubitRef>,
        target: QubitRef,
    },
    Barrier,
}

impl From<Unitary> for UnitaryRef {
    fn from(unitary: Unitary) -> Self {
        Rc::new(RefCell::new(unitary))
    }
}

#[derive(Debug)]
pub struct HashableUnitaryRef {
    pub value: UnitaryRef,
}

impl Eq for HashableUnitaryRef {}

impl From<UnitaryRef> for HashableUnitaryRef {
    fn from(node: UnitaryRef) -> Self {
        Self { value: node }
    }
}

impl Hash for HashableUnitaryRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

impl PartialEq for HashableUnitaryRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}

#[derive(Debug)]
pub enum Qubit {
    ConstTrue,
    ConstFalse,
    QBit {
        name: String,
        dependency: Option<DependencyRef>,
        stack: VecDeque<UnitaryRef>,
    },
}

impl From<Qubit> for QubitRef {
    fn from(gate: Qubit) -> Self {
        Rc::new(RefCell::new(gate))
    }
}

pub type QubitRef = Rc<RefCell<Qubit>>;

#[derive(Debug)]
pub struct HashableQubitRef {
    pub value: QubitRef,
}

impl Eq for HashableQubitRef {}

impl From<QubitRef> for HashableQubitRef {
    fn from(node: QubitRef) -> Self {
        Self { value: node }
    }
}

impl Hash for HashableQubitRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

impl PartialEq for HashableQubitRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}

#[derive(Debug)]
pub struct Dependency {
    name: String,
    operands: Vec<Vec<QubitRef>>,
}

impl From<Dependency> for DependencyRef {
    fn from(unitary: Dependency) -> Self {
        Rc::new(RefCell::new(unitary))
    }
}

impl Dependency {
    pub fn new(name: &str, operand1: &[QubitRef], operand2: &[QubitRef]) -> Self {
        Self {
            name: name.to_string(),
            operands: vec![operand1.to_owned(), operand2.to_owned()],
        }
    }
}

pub type DependencyRef = Rc<RefCell<Dependency>>;
#[derive(Debug)]
pub struct HashableDependencyRef {
    pub value: DependencyRef,
}

impl Eq for HashableDependencyRef {}

impl From<DependencyRef> for HashableDependencyRef {
    fn from(node: DependencyRef) -> Self {
        Self { value: node }
    }
}

impl Hash for HashableDependencyRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

impl PartialEq for HashableDependencyRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}
// END structs declaration

// BEGIN some functions

fn get_qubit_from_constant_bit(bit: u64) -> QubitRef {
    assert!((bit == 0) | (bit == 1));
    if bit == 1 {
        QubitRef::from(Qubit::ConstTrue)
    } else {
        QubitRef::from(Qubit::ConstFalse)
    }
}

fn get_qubitset_from_constant(value: &u64, wordsize: &usize) -> Vec<QubitRef> {
    let mut temp = *value;
    let mut answer = Vec::new();
    for _ in 0..(*wordsize) {
        answer.push(get_qubit_from_constant_bit(temp % 2));
        temp /= 2;
    }
    answer
}

fn get_qubit_from_bool(bit: bool) -> QubitRef {
    if bit {
        QubitRef::from(Qubit::ConstTrue)
    } else {
        QubitRef::from(Qubit::ConstFalse)
    }
}

fn is_constant(qubit_type: &QubitRef) -> bool {
    matches!(&*qubit_type.borrow(), Qubit::ConstFalse | Qubit::ConstTrue)
}

fn get_replacement_from_constant(sort: &NodeType, mut value: u64) -> Vec<QubitRef> {
    let total_bits = sort.bitsize();
    let mut replacement: Vec<QubitRef> = Vec::new();
    for _ in 0..total_bits {
        replacement.push(get_qubit_from_constant_bit(value % 2));
        value /= 2;
    }
    replacement
}

fn get_value_from_constants(qubits: &[QubitRef]) -> u64 {
    let mut answer = 0;
    for (index, qubit) in qubits.iter().enumerate() {
        assert!(is_constant(qubit));

        if let Some(value) = get_constant(qubit) {
            if value {
                answer += 1 << index;
            }
        }
    }
    answer
}

fn are_all_constants(qubits: &[QubitRef]) -> bool {
    for qubit in qubits {
        if get_constant(qubit).is_none() {
            return false;
        }
    }
    true
}

fn get_word_value(
    qubits: &[QubitRef],
    assignment: &HashMap<HashableQubitRef, bool>,
) -> Option<i64> {
    let mut answer: i64 = 0;
    let mut curr_power = 1;
    for qubit in qubits.iter() {
        let key = HashableQubitRef::from(qubit.clone());
        if let Some(value) = assignment.get(&key) {
            answer += curr_power * (*value as i64);
        } else if matches!(&*qubit.borrow(), Qubit::ConstTrue) {
            answer += curr_power;
        } else if !matches!(&*qubit.borrow(), Qubit::ConstFalse) {
            return None;
        }
        curr_power <<= 1;
    }
    Some(answer)
}

fn get_constant(gate_type: &QubitRef) -> Option<bool> {
    match &*gate_type.borrow() {
        Qubit::ConstFalse => Some(false),
        Qubit::ConstTrue => Some(true),
        _ => None,
    }
}

fn are_both_constants(const1: Option<bool>, const2: Option<bool>) -> bool {
    if let Some(_a) = const1 {
        if let Some(_b) = const2 {
            return true;
        }
    }
    false
}

fn are_there_false_constants(consts: Vec<Option<bool>>) -> bool {
    for c in consts.into_iter().flatten() {
        if !c {
            return true;
        }
    }
    false
}

fn are_there_true_constants(consts: Vec<Option<bool>>) -> bool {
    for c in consts.into_iter().flatten() {
        if c {
            return true;
        }
    }
    false
}

fn is_target_in_controls(controls: &[QubitRef], target: &QubitRef) -> bool {
    let key_target = HashableQubitRef::from(target.clone());

    for c in controls.iter() {
        assert!(!is_constant(c));
        let c_key = HashableQubitRef::from(c.clone());

        if c_key == key_target {
            return true;
        }
    }

    false
}

fn prepare_controls_for_mcx(
    controls: &[QubitRef],
    _target: &QubitRef,
) -> (Option<bool>, Vec<QubitRef>) {
    let mut is_used: HashSet<HashableQubitRef> = HashSet::new();
    // is_used.insert(target_key); // TODO: manage properly when target is also control

    let mut result: Vec<QubitRef> = Vec::new();
    for q in controls {
        if !is_constant(q) {
            let key = HashableQubitRef::from(q.clone());
            if !is_used.contains(&key) {
                is_used.insert(key);
                result.push(q.clone());
            }
        } else {
            let val = get_constant(q);
            if are_there_false_constants(vec![val]) {
                return (Some(false), vec![]);
            }
        }
    }

    if result.is_empty() {
        // if !is_target_also_control {
        //     (Some(true), result)
        // } else
        // if let Some(target_value) = get_constant(target) {
        //     if target_value {
        //         (Some(true), result)
        //     } else {
        //         (Some(false), result)
        //     }
        // } else {
        // target is also control
        // (None, result)
        (Some(true), result)
        // }
    } else {
        (None, result)
    }
}

// END some functions

// Begin implementation

pub struct QuantumCircuit<'a> {
    pub bad_state_qubits: Vec<QubitRef>,
    pub bad_state_nodes: Vec<NodeRef>,
    pub all_qubits: HashSet<QubitRef>,
    pub constraints: HashMap<HashableQubitRef, bool>, // this is for remainder and division, these are constraint based.
    pub qubit_to_nid: HashMap<HashableQubitRef, Nid>,
    pub dependencies: HashMap<HashableDependencyRef, Vec<QubitRef>>,
    pub input_qubits: Vec<(NodeRef, Vec<QubitRef>)>,
    pub mapping_nids: HashMap<Nid, NodeRef>,
    pub mapping: HashMap<HashableNodeRef, HashMap<i32, Vec<QubitRef>>>, // maps a btor2 operator to its resulting bitvector of gates
    pub circuit_stack: Vec<UnitaryRef>,
    pub count_multiqubit_gates: u64,
    pub current_n: i32,
    pub current_state_nodes: HashMap<HashableNodeRef, i32>,
    pub result_ored_bad_states: QubitRef,
    pub dynamic_memory: Vec<QubitRef>,
    pub output_oracle: Option<QubitRef>,
    clean_ancillas: HashSet<HashableQubitRef>,
    used_ancillas: HashSet<HashableQubitRef>,
    // pub temp: Vec<QubitRef>,
    word_size: usize,
    model: &'a Model, // BTOR2 model
}

impl<'a> QuantumCircuit<'a> {
    pub fn new(model_: &'a Model, word_size_: usize) -> Self {
        Self {
            bad_state_qubits: Vec::new(),
            bad_state_nodes: Vec::new(),
            constraints: HashMap::new(),
            dependencies: HashMap::new(),
            all_qubits: HashSet::new(),
            input_qubits: Vec::new(),
            mapping_nids: HashMap::new(),
            mapping: HashMap::new(),
            dynamic_memory: Vec::new(),
            circuit_stack: Vec::new(),
            current_state_nodes: HashMap::new(),
            model: model_,
            word_size: word_size_,
            count_multiqubit_gates: 0,
            current_n: 0,
            qubit_to_nid: HashMap::new(),
            clean_ancillas: HashSet::new(),
            used_ancillas: HashSet::new(),
            result_ored_bad_states: QubitRef::from(Qubit::QBit {
                name: "result_or".to_string(),
                dependency: None,
                stack: VecDeque::new(),
            }),
            output_oracle: None,
        }
    }

    fn add_not_gate(
        &mut self,
        qubit: &mut QubitRef,
        gates_to_uncompute_: Option<&mut Vec<UnitaryRef>>,
    ) -> QubitRef {
        if let Some(value) = get_constant(qubit) {
            if value {
                QubitRef::from(Qubit::ConstFalse)
            } else {
                QubitRef::from(Qubit::ConstTrue)
            }
        } else {
            let not_gate = UnitaryRef::from(Unitary::Not {
                input: qubit.clone(),
            });
            self.circuit_stack.push(not_gate.clone());

            self.add_gate_to_qubit_stack(qubit, not_gate.clone());
            if let Some(gates_to_uncompute) = gates_to_uncompute_ {
                gates_to_uncompute.push(not_gate);
            }
            qubit.clone()
        }
    }

    fn add_mcx_gate(
        &mut self,
        controls: Vec<&mut QubitRef>,
        target: &mut QubitRef,
        gates_to_uncompute_: Option<&mut Vec<UnitaryRef>>,
    ) {
        let non_mutable_vec = controls
            .into_iter()
            .map(|x| (*x).clone())
            .collect::<Vec<QubitRef>>();
        let mcx_gate = UnitaryRef::from(Unitary::Mcx {
            controls: non_mutable_vec,
            target: target.clone(),
        });

        self.circuit_stack.push(mcx_gate.clone());

        self.add_gate_to_qubit_stack(target, mcx_gate.clone());
        if let Some(gates_to_uncompute) = gates_to_uncompute_ {
            gates_to_uncompute.push(mcx_gate);
        }
    }

    fn not_gate(&mut self, a_qubit: &mut QubitRef) -> QubitRef {
        if let Some(a_const) = get_constant(a_qubit) {
            if a_const {
                QubitRef::from(Qubit::ConstFalse)
            } else {
                QubitRef::from(Qubit::ConstTrue)
            }
        } else {
            //  since we dont know whether this qubit is going to be used later
            let mut target = self.get_rom(None);

            assert!(!is_constant(&target));

            target = self.add_not_gate(&mut target, None);
            self.add_mcx_gate(vec![a_qubit], &mut target, None);
            target
        }
    }

    fn is_qubit_rom(&self, qubit: &QubitRef) -> bool {
        let key = HashableQubitRef::from(qubit.clone());
        !self.clean_ancillas.contains(&key) && !self.used_ancillas.contains(&key)
    }

    fn is_rom(&self, replacement: &[QubitRef]) -> bool {
        for r in replacement.iter() {
            if !self.is_qubit_rom(r) {
                return false;
            }
        }
        true
    }

    fn get_last_qubitset(&self, node: &NodeRef) -> Option<Vec<QubitRef>> {
        let key = HashableNodeRef::from(node.clone());

        if !self.mapping.contains_key(&key) {
            None
        } else {
            match *node.borrow() {
                Node::Const { .. } => {
                    if self.mapping.get(&key).unwrap().contains_key(&0) {
                        Some(self.mapping.get(&key).cloned().unwrap()[&0].clone())
                    } else {
                        None
                    }
                }
                Node::State { .. } | Node::Input { .. } => {
                    let replacements = self.mapping.get(&key).unwrap();
                    if let Some(replacement) = replacements.get(&(self.current_n - 1)) {
                        assert!(self.is_rom(replacement));
                        Some(replacement.clone())
                    } else {
                        let node_hash = HashableNodeRef::from(node.clone());
                        let index = self.current_state_nodes[&node_hash];
                        assert!(self.is_rom(&replacements[&index].clone()));
                        Some(replacements[&index].clone())
                    }
                }
                Node::Next { .. } | Node::Bad { .. } => None,
                _ => {
                    let replacements = self.mapping.get(&key).unwrap();
                    if replacements.contains_key(&self.current_n) {
                        assert!(self.is_rom(&replacements[&self.current_n].clone()));
                        Some(replacements[&self.current_n].clone())
                    } else {
                        None
                    }
                }
            }
        }
    }

    fn or_bad_state_qubits(&mut self, controls: Vec<QubitRef>, target: &QubitRef) {
        // This function assumes optimizations before calling it, since its only used for the output of the oracle.
        // assume all values are Qubit::Qbit
        assert!(controls.len() > 1);
        assert!(!is_constant(target));
        self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
            input: target.clone(),
        }));

        for qubit in controls.iter() {
            assert!(!is_constant(qubit));
            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                input: qubit.clone(),
            }));
        }

        self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
            controls,
            target: target.clone(),
        }));
        for qubit in self.bad_state_qubits.clone() {
            assert!(!is_constant(&qubit));
            self.circuit_stack
                .push(UnitaryRef::from(Unitary::Not { input: qubit }));
        }
    }

    fn _are_all_ancillas_clean(&self) -> bool {
        self.used_ancillas.is_empty()
    }

    fn apply_mcx_gate_for_target_in_controls(
        &mut self,
        controls_: &mut [QubitRef],
        target: &QubitRef,
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
    ) -> QubitRef {
        assert!(!is_constant(target));
        if controls_.len() == 1 {
            QubitRef::from(Qubit::ConstFalse)
        } else {
            let mut controls = Vec::new();

            let target_key = HashableQubitRef::from(target.clone());
            for c in controls_.iter() {
                let c_key = HashableQubitRef::from(c.clone());
                if c_key != target_key {
                    controls.push(c.clone());
                }
            }
            let mut local_gates_to_uncompute: Vec<UnitaryRef> = Vec::new();

            let mut ancilla_controls = self.get_memory();
            self.add_mcx_gate(
                controls.iter_mut().collect(),
                &mut target.clone(),
                Some(&mut local_gates_to_uncompute),
            );
            ancilla_controls =
                self.add_not_gate(&mut ancilla_controls, Some(&mut local_gates_to_uncompute));

            let mut qubit_out = if is_rom {
                self.get_rom(None)
            } else {
                self.get_memory()
            };

            if !is_rom {
                for gate in local_gates_to_uncompute {
                    gates_to_uncompute.push(gate);
                }
                self.add_mcx_gate(
                    vec![&mut ancilla_controls, &mut target.clone()],
                    &mut qubit_out,
                    Some(gates_to_uncompute),
                );
            } else {
                self.add_mcx_gate(
                    vec![&mut ancilla_controls, &mut target.clone()],
                    &mut qubit_out,
                    None,
                );
                let prev_length = self.used_ancillas.len();
                self.uncompute(&local_gates_to_uncompute);
                assert!(self.used_ancillas.len() == prev_length - 1);
            }
            qubit_out
        }
    }

    fn apply_mcx_gate(
        &mut self,
        controls_: &mut [QubitRef],
        target_: &Option<QubitRef>,
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
        allow_push: bool,
    ) -> QubitRef {
        let mut target = if let Some(qubit) = target_ {
            if is_rom && !self.is_qubit_rom(qubit) {
                let new_target = QubitRef::from(Qubit::QBit {
                    name: "".to_string(),
                    dependency: None,
                    stack: VecDeque::new(),
                });
                self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                    control: qubit.clone(),
                    target: new_target.clone(),
                }));
                new_target
            } else {
                qubit.clone()
            }
        } else {
            QubitRef::from(Qubit::ConstFalse)
        };

        if is_rom {
            assert!(self.is_qubit_rom(&target));
        }

        let (value_, mut controls) = prepare_controls_for_mcx(controls_, &target);

        if is_target_in_controls(&controls, &target) {
            return self.apply_mcx_gate_for_target_in_controls(
                &mut controls,
                &target,
                gates_to_uncompute,
                is_rom,
            );
        }

        if let Some(value) = value_ {
            if value {
                // all controls are true
                if let Some(target_val) = get_constant(&target) {
                    // all controls are true and target is a constant
                    if target_val {
                        QubitRef::from(Qubit::ConstFalse)
                    } else {
                        QubitRef::from(Qubit::ConstTrue)
                    }
                } else {
                    if !is_rom {
                        target = self.add_not_gate(&mut target, Some(gates_to_uncompute));
                    } else {
                        assert!(self.is_qubit_rom(&target));
                        target = self.add_not_gate(&mut target, None);
                    }
                    target
                }
            } else {
                // at least one control is false
                if is_rom {
                    assert!(self.is_qubit_rom(&target));
                }
                target
            }
        } else {
            let target_ghost_value = if let Some(v) = get_constant(&target) {
                if allow_push {
                    v
                } else {
                    true
                }
            } else {
                true
            };

            if controls.len() == 1 && !target_ghost_value {
                controls[0].clone()
            } else {
                let mut target_final;
                if let Some(target_value) = get_constant(&target) {
                    if is_rom {
                        target_final = self.get_rom(None);
                    } else {
                        target_final = self.get_memory();
                    }

                    if target_value {
                        if !is_rom {
                            target_final =
                                self.add_not_gate(&mut target_final, Some(gates_to_uncompute));
                        } else {
                            target_final = self.add_not_gate(&mut target_final, None);
                        }
                    }
                    if !is_rom {
                        self.add_mcx_gate(
                            controls.iter_mut().collect(),
                            &mut target_final,
                            Some(gates_to_uncompute),
                        );
                    } else {
                        self.add_mcx_gate(controls.iter_mut().collect(), &mut target_final, None);
                    }
                } else {
                    target_final = target;
                    if !is_rom {
                        self.add_mcx_gate(
                            controls.iter_mut().collect(),
                            &mut target_final,
                            Some(gates_to_uncompute),
                        );
                    } else {
                        self.add_mcx_gate(controls.iter_mut().collect(), &mut target_final, None);
                    }
                }
                if is_rom {
                    assert!(self.is_qubit_rom(&target_final));
                }
                target_final
            }
        }
    }

    fn record_mapping(
        &mut self,
        node: &NodeRef,
        index: i32,
        replacement: Vec<QubitRef>,
    ) -> Vec<QubitRef> {
        let key = HashableNodeRef::from(node.clone());

        if !self.mapping.contains_key(&key) {
            self.mapping.insert(key.clone(), HashMap::new());
        }

        let replacements = self.mapping.get_mut(&key).unwrap();
        replacements.insert(index, replacement.clone());
        self.current_state_nodes.insert(key, index);

        replacement
    }

    fn process_input(&mut self, sort: usize, node: &NodeRef, _name: String) -> Vec<QubitRef> {
        if let Some(replacement) = self.get_last_qubitset(node) {
            replacement
        } else {
            let mut replacement: Vec<QubitRef> = Vec::new();
            for _ in 0..sort {
                replacement.push(self.get_rom(None));
            }
            self.input_qubits.push((node.clone(), replacement.clone()));
            assert!(replacement.len() == sort);
            assert!(self.is_rom(&replacement));
            self.record_mapping(node, self.current_n, replacement)
        }
    }
    fn pop_back_qubit_stack(&mut self, qubit: &QubitRef, gate: &UnitaryRef) {
        // assert!(!self.is_qubit_rom(qubit));

        match *qubit.borrow_mut() {
            Qubit::QBit { ref mut stack, .. } => {
                assert!(!stack.is_empty());
                let qubit_key = HashableQubitRef::from(qubit.clone());
                let gate_qubit_stack = stack.pop_back().unwrap();
                let gate_key = HashableUnitaryRef::from(gate.clone());
                let gate_qubit = HashableUnitaryRef::from(gate_qubit_stack);
                assert!(gate_key == gate_qubit);

                if stack.is_empty() && !self.is_qubit_rom(qubit) {
                    assert!(self.used_ancillas.contains(&qubit_key));
                    self.used_ancillas.remove(&qubit_key);
                    self.clean_ancillas.insert(qubit_key);
                }
            }
            _ => panic!("Trying to pop stack of constant qubit!"),
        }
    }

    fn get_dependency(&self, qubit: &QubitRef) -> Option<DependencyRef> {
        match &*qubit.borrow() {
            Qubit::QBit { dependency, .. } => dependency.clone(),
            _ => None,
        }
    }

    fn get_qubit_stack_length(&mut self, qubit: &QubitRef) -> usize {
        match &*qubit.borrow() {
            Qubit::QBit { stack, .. } => stack.len(),
            _ => panic!("Trying to get length of constant bit"),
        }
    }

    fn get_safe_uncomputable_rom(
        &mut self,
        gates_to_uncompute: &[UnitaryRef],
        replacement: &[QubitRef],
    ) -> Vec<QubitRef> {
        let mut new_replacement = Vec::new();

        let mut non_const_qubits = HashSet::new();
        for gate in gates_to_uncompute.iter() {
            if let Some(qubit) = self.get_qubit_to_uncompute(gate) {
                let qubit_key = HashableQubitRef::from(qubit.clone());
                non_const_qubits.insert(qubit_key);
            }
        }

        for r in replacement.iter() {
            let r_key = HashableQubitRef::from(r.clone());
            assert!(self.is_qubit_rom(r));
            if non_const_qubits.contains(&r_key) {
                let dep = self.get_dependency(r);
                let new_qubit = self.get_rom(dep);
                self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                    control: r.clone(),
                    target: new_qubit.clone(),
                }));
                new_replacement.push(new_qubit);
            } else {
                new_replacement.push(r.clone());
            }
        }
        assert!(new_replacement.len() == replacement.len());
        new_replacement
    }

    fn get_qubit_to_uncompute(&self, gate: &UnitaryRef) -> Option<QubitRef> {
        match &*gate.borrow() {
            Unitary::Not { input } => Some(input.clone()),
            Unitary::Cnot { control: _, target } => Some(target.clone()),
            Unitary::Mcx {
                controls: _,
                target,
            } => Some(target.clone()),
            Unitary::Barrier => None,
        }
    }

    fn uncompute(&mut self, gates_to_uncompute: &[UnitaryRef]) {
        for gate in gates_to_uncompute.iter().rev() {
            self.circuit_stack.push(gate.clone());
            if let Some(qubit) = self.get_qubit_to_uncompute(gate) {
                let previous_length = self.get_qubit_stack_length(&qubit);
                self.pop_back_qubit_stack(&qubit, gate);
                assert!(previous_length - 1 == self.get_qubit_stack_length(&qubit));
            }
        }
    }

    fn get_rom(&mut self, dependency_: Option<DependencyRef>) -> QubitRef {
        if let Some(dependency) = dependency_ {
            QubitRef::from(Qubit::QBit {
                name: "".to_string(),
                dependency: Some(dependency),
                stack: VecDeque::new(),
            })
        } else {
            QubitRef::from(Qubit::QBit {
                name: "".to_string(),
                dependency: None,
                stack: VecDeque::new(),
            })
        }
    }

    fn get_one_clean_ancilla(&mut self) -> QubitRef {
        if self.clean_ancillas.is_empty() {
            panic!("There are no ancillas");
        }
        let element = self.clean_ancillas.iter().next().unwrap();
        element.value.clone()
    }

    fn get_memory(&mut self) -> QubitRef {
        if self.clean_ancillas.is_empty() {
            let key = HashableQubitRef::from(QubitRef::from(Qubit::QBit {
                name: "".to_string(),
                dependency: None,
                stack: VecDeque::new(),
            }));
            self.clean_ancillas.insert(key);
        }

        let qubit = self.get_one_clean_ancilla();

        match &*qubit.borrow() {
            Qubit::QBit { stack, .. } => {
                assert!(stack.is_empty());
            }
            _ => {
                panic!("memory has constant value!");
            }
        }
        let key = HashableQubitRef::from(qubit.clone());
        self.clean_ancillas.remove(&key);
        self.used_ancillas.insert(key);
        qubit
    }

    fn add_one_qubitset(
        &mut self,
        qubitset: &[QubitRef],
        target_set: Vec<QubitRef>,
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
    ) -> Vec<QubitRef> {
        let mut result: Vec<QubitRef> = vec![];

        let sort = qubitset.len();
        assert!(target_set.len() == qubitset.len());

        for qubit in target_set.iter() {
            result.push(qubit.clone());
        }

        for index in 0..sort {
            for i in index..sort {
                let mut controls = result[index..((sort - 1 - i) + index)].to_vec();
                controls.push(qubitset[index].clone());
                let target = result[sort - 1 - i + index].clone();

                result[sort - 1 - i + index] = self.apply_mcx_gate(
                    &mut controls,
                    &Some(target),
                    gates_to_uncompute,
                    is_rom,
                    false,
                );
            }
        }
        assert!(result.len() == sort);
        result
    }

    fn add_gate_to_qubit_stack(&mut self, qubit: &mut QubitRef, gate: UnitaryRef) {
        let key = HashableQubitRef::from(qubit.clone());
        self.clean_ancillas.remove(&key);

        assert!(!self.clean_ancillas.contains(&key));
        match *qubit.borrow_mut() {
            Qubit::QBit { ref mut stack, .. } => {
                let prev_length = stack.len();
                stack.push_back(gate);
                assert!(stack.len() == prev_length + 1);
            }
            _ => panic!("parameter of this function should not be a constant value"),
        }
    }

    fn add(
        &mut self,
        left_operand: &[QubitRef],
        right_operand: &[QubitRef],
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
    ) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let mut replacement: Vec<QubitRef> = vec![];

        // initially replacement is |0>
        for _ in 0..left_operand.len() {
            replacement.push(QubitRef::from(Qubit::ConstFalse));
        }

        // replacement += left_operand
        replacement = self.add_one_qubitset(left_operand, replacement, gates_to_uncompute, false);

        // replacement += right_operand
        replacement = self.add_one_qubitset(right_operand, replacement, gates_to_uncompute, is_rom);
        assert!(replacement.len() == left_operand.len());
        replacement
    }

    fn sub(
        &mut self,
        left_operand: &[QubitRef],
        right_operand: &[QubitRef],
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
    ) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let (to_uncompute, negated_right) = self.twos_complement(right_operand);

        let replacement = self.add(left_operand, &negated_right, gates_to_uncompute, is_rom);

        // uncompute twos complement
        for gate in to_uncompute.iter().rev() {
            self.circuit_stack.push(gate.clone());
        }

        assert!(replacement.len() == left_operand.len());
        replacement
    }

    fn twos_complement(&mut self, qubitset: &[QubitRef]) -> (Vec<UnitaryRef>, Vec<QubitRef>) {
        let mut gates_to_uncompute: Vec<UnitaryRef> = Vec::new();
        let mut result1: Vec<QubitRef> = Vec::new();

        for qubit in qubitset {
            if let Some(val) = get_constant(qubit) {
                if val {
                    result1.push(QubitRef::from(Qubit::ConstFalse));
                } else {
                    result1.push(QubitRef::from(Qubit::ConstTrue));
                }
            } else {
                result1.push(qubit.clone());
                assert!(!is_constant(qubit));
                gates_to_uncompute.push(UnitaryRef::from(Unitary::Not {
                    input: qubit.clone(),
                }));
                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                    input: qubit.clone(),
                }));
            }
        }
        assert!(result1.len() == qubitset.len());
        let sort = qubitset.len();
        for i in 0..sort - 1 {
            let target = result1[sort - i - 1].clone();
            let mut controls = result1[..(sort - i - 1)].to_vec();
            result1[sort - i - 1] = self.apply_mcx_gate(
                &mut controls,
                &Some(target),
                &mut gates_to_uncompute,
                false,
                false,
            );
        }

        assert!(result1.len() == qubitset.len());

        // apply not gate to LSB qubit
        if let Some(val) = get_constant(&result1[0]) {
            result1[0] = get_qubit_from_bool(!val);
        } else {
            assert!(!is_constant(&result1[0]));
            gates_to_uncompute.push(UnitaryRef::from(Unitary::Not {
                input: result1[0].clone(),
            }));
            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                input: result1[0].clone(),
            }));
        }

        (gates_to_uncompute, result1)
    }

    fn multiply_word_by_bit(
        &mut self,
        word: &[QubitRef],
        bit: &QubitRef,
        shift: usize,
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
    ) -> Vec<QubitRef> {
        let mut result: Vec<QubitRef> = Vec::new();

        let mut s = 0;
        let mut i = 0;
        if let Some(val) = get_constant(bit) {
            if val {
                while result.len() < word.len() {
                    if s < shift {
                        result.push(QubitRef::from(Qubit::ConstFalse));
                        s += 1;
                    } else {
                        result.push(word[i].clone());
                        i += 1;
                    }
                }
            } else {
                while result.len() < word.len() {
                    result.push(QubitRef::from(Qubit::ConstFalse));
                }
            }
            result
        } else {
            while result.len() < word.len() {
                if s < shift {
                    result.push(QubitRef::from(Qubit::ConstFalse));
                    s += 1;
                } else {
                    if let Some(val) = get_constant(&word[i]) {
                        if val {
                            result.push(bit.clone());
                        } else {
                            result.push(QubitRef::from(Qubit::ConstFalse));
                        }
                    } else {
                        let target = self.apply_mcx_gate(
                            &mut [word[i].clone(), bit.clone()],
                            &None,
                            gates_to_uncompute,
                            is_rom,
                            false,
                        );
                        result.push(target.clone());
                    }
                    i += 1;
                }
            }
            assert!(result.len() == word.len());
            result
        }
    }

    fn mul(
        &mut self,
        left_operand: &[QubitRef],
        right_operand: &[QubitRef],
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
    ) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let mut replacement: Vec<QubitRef> = Vec::new();

        for _ in 0..left_operand.len() {
            replacement.push(QubitRef::from(Qubit::ConstFalse));
        }
        for (index, bit) in left_operand.iter().enumerate() {
            let result =
                self.multiply_word_by_bit(right_operand, bit, index, gates_to_uncompute, false);

            if index + 1 == left_operand.len() {
                replacement =
                    self.add_one_qubitset(&result, replacement, gates_to_uncompute, is_rom);
            } else {
                replacement =
                    self.add_one_qubitset(&result, replacement, gates_to_uncompute, false);
            }
        }
        assert!(replacement.len() == left_operand.len());
        replacement
    }

    fn eq(
        &mut self,
        left_operand: &[QubitRef],
        right_operand: &[QubitRef],
        _nid: &Nid,
        _prefix: String,
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
        allow_push: bool,
    ) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let mut controls: Vec<QubitRef> = vec![];
        let mut qubits_to_not: HashSet<HashableQubitRef> = HashSet::new();
        let mut qubit_to_not_vec: Vec<QubitRef> = Vec::new();

        for (l_qubit, r_qubit) in left_operand.iter().zip(right_operand.iter()) {
            let const_l = get_constant(l_qubit);
            let const_r = get_constant(r_qubit);

            if are_both_constants(const_l, const_r) {
                if const_l.unwrap() != const_r.unwrap() {
                    return vec![QubitRef::from(Qubit::ConstFalse)];
                }
            } else if are_there_true_constants(vec![const_l, const_r]) {
                if is_constant(l_qubit) {
                    controls.push(r_qubit.clone());
                } else {
                    controls.push(l_qubit.clone());
                }
            } else if are_there_false_constants(vec![const_l, const_r]) {
                let control: QubitRef = if is_constant(l_qubit) {
                    r_qubit.clone()
                } else {
                    l_qubit.clone()
                };

                let target: QubitRef = self.apply_mcx_gate(
                    &mut [control.clone()],
                    &None,
                    gates_to_uncompute,
                    false,
                    allow_push,
                );
                // controls.push(target.clone());
                assert!(!is_constant(&target));
                let target_key = HashableQubitRef::from(target.clone());
                if !qubits_to_not.contains(&target_key) {
                    qubits_to_not.insert(target_key);
                    qubit_to_not_vec.push(target);
                }

                // self.add_not_gate(&mut target, Some(gates_to_uncompute));
            } else {
                // no constants
                let mut target: QubitRef = self.apply_mcx_gate(
                    &mut [l_qubit.clone()],
                    &None,
                    gates_to_uncompute,
                    false,
                    allow_push,
                );

                assert!(!is_constant(&target));

                target = self.apply_mcx_gate(
                    &mut [r_qubit.clone()],
                    &Some(target.clone()),
                    gates_to_uncompute,
                    false,
                    true,
                );

                // target = self.add_not_gate(&mut target, Some(gates_to_uncompute));
                // controls.push(target.clone());
                let target_key = HashableQubitRef::from(target.clone());
                if !qubits_to_not.contains(&target_key) {
                    qubits_to_not.insert(target_key);
                    qubit_to_not_vec.push(target);
                }
            }
        }

        for q in qubit_to_not_vec.iter_mut() {
            controls.push(self.add_not_gate(q, Some(gates_to_uncompute)));
        }

        let replacement =
            vec![self.apply_mcx_gate(&mut controls, &None, gates_to_uncompute, is_rom, allow_push)];
        assert!(replacement.len() == 1);
        replacement
    }

    fn insert_into_constraints(&mut self, qubit: &QubitRef, value: bool) {
        let key = HashableQubitRef::from(qubit.clone());
        if let std::collections::hash_map::Entry::Vacant(e) = self.constraints.entry(key) {
            e.insert(value);
        } else {
            let key = HashableQubitRef::from(qubit.clone());
            assert!(value == *self.constraints.get(&key).unwrap());
        }
    }

    fn div(
        &mut self,
        left: &NodeRef,
        right: &NodeRef,
        nid: &Nid,
    ) -> (Vec<QubitRef>, Vec<QubitRef>) {
        let mut left_operand = self.process(left);
        let mut right_operand = self.process(right);
        assert!(self.is_rom(&left_operand));
        assert!(self.is_rom(&right_operand));

        assert!(left_operand.len() == right_operand.len());

        if are_all_constants(&left_operand) && are_all_constants(&right_operand) {
            let value_left = get_value_from_constants(&left_operand);
            let value_right = get_value_from_constants(&right_operand);

            if value_right == 0 {
                panic!("There is a division by zero in this program!");
            }

            let coeff_dec = value_left / value_right;
            let rem_dec = value_left % value_right;

            let wordsize = left_operand.len();
            let coeff_qubitset = get_qubitset_from_constant(&coeff_dec, &wordsize);
            let rem_qubitset = get_qubitset_from_constant(&rem_dec, &wordsize);

            (coeff_qubitset, rem_qubitset)
        } else {
            let mut c: Vec<QubitRef> = Vec::new();
            let mut r: Vec<QubitRef> = Vec::new();

            left_operand.push(QubitRef::from(Qubit::ConstFalse));
            right_operand.push(QubitRef::from(Qubit::ConstFalse));

            let sort = left_operand.len();
            let mut i = 0;

            let coeff_dep =
                DependencyRef::from(Dependency::new("div", &left_operand, &right_operand));
            let rem_dep =
                DependencyRef::from(Dependency::new("rem", &left_operand, &right_operand));
            while c.len() < sort {
                c.push(QubitRef::from(Qubit::QBit {
                    name: format!("{}_coeff{}_{}", nid, i, self.current_n),
                    dependency: Some(coeff_dep.clone()),
                    stack: VecDeque::new(),
                }));
                r.push(QubitRef::from(Qubit::QBit {
                    name: format!("{}_rem{}_{}", nid, i, self.current_n),
                    dependency: Some(rem_dep.clone()),
                    stack: VecDeque::new(),
                }));
                i += 1;
            }

            let mut key = HashableDependencyRef::from(coeff_dep);
            self.dependencies.insert(key, c.clone());

            key = HashableDependencyRef::from(rem_dep);
            self.dependencies.insert(key, r.clone());

            let mut gates_to_uncompute = Vec::new();
            let res_mul = self.mul(&right_operand, &c, &mut gates_to_uncompute, false);

            let res_sum = self.add(&res_mul, &r, &mut gates_to_uncompute, false);

            let res_eq = self.eq(
                &res_sum,
                &left_operand,
                nid,
                "div_eq".to_string(),
                &mut gates_to_uncompute,
                false,
                false,
            );
            assert!(res_eq.len() == 1);

            let mut gates_to_uncompute = Vec::new();
            let res_ult = self.ult(&r, &right_operand, &true, &mut gates_to_uncompute, false);

            let mut true_constraints_target = self.apply_mcx_gate(
                &mut [res_eq[0].clone(), res_ult[res_ult.len() - 1].clone()],
                &None,
                &mut gates_to_uncompute,
                true,
                false,
            );

            {
                // add the following constraints:
                //  left = right*coeff + rem
                //  rem < right
                if let Some(value) = get_constant(&true_constraints_target) {
                    if !value {
                        panic!("constraints are never met")
                    }
                } else {
                    // check right operand cannot be zero
                    let mut dummy_zero: Vec<QubitRef> = Vec::new();

                    for _ in 0..right_operand.len() {
                        dummy_zero.push(QubitRef::from(Qubit::ConstFalse));
                    }

                    let eq_dummy_zero = self.eq(
                        &dummy_zero,
                        &right_operand,
                        nid,
                        "div_eq_dummy_zero".to_string(),
                        &mut gates_to_uncompute,
                        false,
                        false,
                    );
                    assert!(eq_dummy_zero.len() == 1);

                    if let Some(div_zero_dummy) = get_constant(&eq_dummy_zero[0]) {
                        if div_zero_dummy {
                            panic!("There is a division by zero!");
                        }
                        assert!(self.is_qubit_rom(&true_constraints_target));
                        true_constraints_target = self.get_safe_uncomputable_rom(
                            &gates_to_uncompute,
                            &[true_constraints_target.clone()],
                        )[0]
                        .clone();
                        self.insert_into_constraints(&true_constraints_target, true);
                    } else {
                        let mut all_constraints_target = self.get_rom(None);

                        // or eq_dummy_zero and true constraints
                        let key_zero_dummy = HashableQubitRef::from(eq_dummy_zero[0].clone());
                        let key_true_constraints =
                            HashableQubitRef::from(true_constraints_target.clone());

                        // NOT operands
                        self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                            input: true_constraints_target.clone(),
                        }));
                        if key_zero_dummy != key_true_constraints {
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                input: eq_dummy_zero[0].clone(),
                            }));
                        }

                        // NOT target
                        let key_all_constraints =
                            HashableQubitRef::from(all_constraints_target.clone());
                        assert!(key_all_constraints != key_zero_dummy);
                        assert!(key_all_constraints != key_true_constraints);
                        self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                            input: all_constraints_target.clone(),
                        }));

                        // PERFORM MCX (logic or)
                        let (value, controls) = prepare_controls_for_mcx(
                            &[true_constraints_target.clone(), eq_dummy_zero[0].clone()],
                            &all_constraints_target,
                        );
                        assert!(value.is_none());

                        self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                            controls,
                            target: all_constraints_target.clone(),
                        }));
                        assert!(self.is_qubit_rom(&all_constraints_target));
                        all_constraints_target = self.get_safe_uncomputable_rom(
                            &gates_to_uncompute,
                            &[all_constraints_target.clone()],
                        )[0]
                        .clone();
                        self.insert_into_constraints(&all_constraints_target, true);

                        // Uncompute NOT on operands
                        self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                            input: true_constraints_target.clone(),
                        }));
                        if key_zero_dummy != key_true_constraints {
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                input: eq_dummy_zero[0].clone(),
                            }));
                        }
                    }
                }
            }

            {
                // add overflow constraints
                let overflow_qubit_sum = res_sum[res_sum.len() - 1].clone();
                let overflow_qubit_mul = res_mul[res_mul.len() - 1].clone();
                assert!(res_sum.len() == res_mul.len());

                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                    input: overflow_qubit_mul.clone(),
                }));

                let key_sum = HashableQubitRef::from(overflow_qubit_sum.clone());
                let key_mul = HashableQubitRef::from(overflow_qubit_mul.clone());
                if key_sum != key_mul {
                    self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                        input: overflow_qubit_sum.clone(),
                    }));
                }
                let target = self.get_rom(None);
                let (value_, controls) = prepare_controls_for_mcx(
                    &[overflow_qubit_sum.clone(), overflow_qubit_mul.clone()],
                    &target,
                );

                if let Some(value) = value_ {
                    if !value {
                        panic!("overflow constraints are never met!!!");
                    }
                } else {
                    assert!(self.is_qubit_rom(&target));
                    self.insert_into_constraints(&target, true);
                    self.circuit_stack
                        .push(UnitaryRef::from(Unitary::Mcx { controls, target }));
                }

                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                    input: overflow_qubit_mul,
                }));
                if key_sum != key_mul {
                    self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                        input: overflow_qubit_sum,
                    }));
                }
            }

            assert!(c.len() == r.len());
            assert!(c.len() == right_operand.len());
            let c_answer = c[..(sort - 1)].to_vec();
            let r_answer = r[..(sort - 1)].to_vec();
            assert!(c_answer.len() == r_answer.len());
            assert!(self.is_rom(&c_answer));
            assert!(self.is_rom(&r_answer));
            self.uncompute(&gates_to_uncompute);
            (c_answer, r_answer)
        }
    }

    pub fn _get_value_from_nid(
        &self,
        nid: Nid,
        assignments: &HashMap<HashableQubitRef, bool>,
    ) -> Option<i64> {
        let node = self.mapping_nids.get(&nid).unwrap();
        let node_hash = HashableNodeRef::from(node.clone());
        self.current_state_nodes.get(&node_hash)?;
        let index = self.current_state_nodes.get(&node_hash).unwrap();

        let replacements = self.mapping.get(&node_hash).unwrap();

        let qubits = replacements[index].clone();
        let mut current_power = 1;

        let mut answer = 0;
        for qubit in qubits {
            let key = HashableQubitRef::from(qubit.clone());
            if let Some(value) = assignments.get(&key) {
                answer += (*value as i64) * current_power;
            } else if let Some(v) = get_constant(&qubit.clone()) {
                answer += (v as i64) * current_power;
            } else {
                return None;
            }
            current_power <<= 1;
        }
        Some(answer)
    }

    fn print_stats(&self) {
        let mut count_gates = 0;
        let mut count_multiqubit_gates = 0;
        let mut count_single_qubit_gates = 0;
        let mut count_qubits = 2; // For qubit const false, and const true
        let mut max_mcx_length = 0;

        let mut qubits_used: HashSet<HashableQubitRef> = HashSet::new();

        for gate in self.circuit_stack.iter() {
            match &*gate.borrow() {
                Unitary::Not { input } => {
                    count_gates += 1;
                    if !is_constant(input) {
                        let key = HashableQubitRef::from(input.clone());
                        if !qubits_used.contains(&key) {
                            count_qubits += 1;
                            qubits_used.insert(key);
                        }
                    }

                    count_single_qubit_gates += 1;
                }
                Unitary::Cnot { control, target } => {
                    count_gates += 1;
                    if !is_constant(control) {
                        let key_control = HashableQubitRef::from(control.clone());

                        if !qubits_used.contains(&key_control) {
                            count_qubits += 1;
                            qubits_used.insert(key_control);
                        }
                    }

                    if !is_constant(target) {
                        let key_target = HashableQubitRef::from(target.clone());
                        if !qubits_used.contains(&key_target) {
                            count_qubits += 1;
                            qubits_used.insert(key_target);
                        }
                    }
                    max_mcx_length = max(max_mcx_length, 1);
                    count_multiqubit_gates += 1;
                }
                Unitary::Mcx { controls, target } => {
                    count_gates += 1;
                    max_mcx_length = max(max_mcx_length, controls.len());
                    for control in controls.iter() {
                        if !is_constant(control) {
                            let key_control = HashableQubitRef::from(control.clone());

                            if !qubits_used.contains(&key_control) {
                                count_qubits += 1;
                                qubits_used.insert(key_control);
                            }
                        }
                    }

                    if !is_constant(target) {
                        let key_target = HashableQubitRef::from(target.clone());
                        if !qubits_used.contains(&key_target) {
                            count_qubits += 1;
                            qubits_used.insert(key_target);
                        }
                    }

                    count_multiqubit_gates += 1;
                }
                _ => {}
            }
        }

        println!("******* QUANTUM CIRCUIT STATS ********");
        println!("Qubits required: {}", count_qubits);
        println!("Total gates: {}", count_gates);
        println!("Single-qubit gates: {}", count_single_qubit_gates);
        println!("MCX gates: {}", count_multiqubit_gates);
        println!("Max. controls in MCX: {}", max_mcx_length);
        println!("**************************************");
    }

    fn ult(
        &mut self,
        left: &[QubitRef],
        right: &[QubitRef],
        is_division: &bool,
        gates_to_uncompute: &mut Vec<UnitaryRef>,
        is_rom: bool,
    ) -> Vec<QubitRef> {
        let mut left_operand = left.to_owned();
        let mut right_operand = right.to_owned();
        if !is_division {
            left_operand.push(QubitRef::from(Qubit::ConstFalse));
            right_operand.push(QubitRef::from(Qubit::ConstFalse));
        }
        self.sub(&left_operand, &right_operand, gates_to_uncompute, is_rom)
    }

    fn process(&mut self, node: &NodeRef) -> Vec<QubitRef> {
        if let Some(replacement) = self.get_last_qubitset(node) {
            return replacement;
        }
        self.mapping_nids.insert(get_nid(node), node.clone());
        match &*node.borrow() {
            Node::Const { sort, imm, .. } => {
                let replacement = get_replacement_from_constant(sort, *imm);
                assert!(replacement.len() == sort.bitsize());
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, 0, replacement)
            }
            Node::State {
                init: None,
                sort,
                name,
                ..
            } => {
                // this is an input
                let name = name.as_deref().unwrap_or("?");
                self.process_input(sort.bitsize(), node, name.to_string())
            }
            Node::Input { sort, name, .. } => {
                self.process_input(sort.bitsize(), node, name.to_string())
            }
            Node::State { sort, init, .. } => {
                // This is a normal state
                let mut replacement = Vec::new();
                if let Some(value) = init {
                    replacement = self.process(value);
                } else {
                    for _ in 0..sort.bitsize() {
                        replacement.push(QubitRef::from(Qubit::ConstFalse));
                    }
                }
                assert!(replacement.len() == sort.bitsize());
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, 0, replacement)
            }
            Node::Not { value, .. } => {
                let mut bitvector = self.process(value);
                assert!(self.is_rom(&bitvector));
                let mut replacement: Vec<QubitRef> = Vec::new();
                for bit in bitvector.iter_mut() {
                    replacement.push(self.not_gate(bit));
                }
                assert!(replacement.len() == bitvector.len());
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Bad { cond, nid, .. } => {
                self.circuit_stack.push(UnitaryRef::from(Unitary::Barrier));
                let replacement = self.process(cond);
                assert!(replacement.len() == 1);
                if get_constant(&replacement[0]).is_none() {
                    let key = HashableQubitRef::from(replacement[0].clone());
                    self.qubit_to_nid.insert(key, *nid);
                }
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::And { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                assert!(self.is_rom(&left_operand));
                assert!(self.is_rom(&right_operand));
                let mut replacement: Vec<QubitRef> = vec![];
                assert!(left_operand.len() == right_operand.len());
                let mut gates_to_uncompute = Vec::new();
                for (l_qubit, r_qubit) in left_operand.iter().zip(right_operand.iter()) {
                    let const_l = get_constant(l_qubit);
                    let const_r = get_constant(r_qubit);
                    if are_both_constants(const_l, const_r) {
                        let val = const_l.unwrap() && const_r.unwrap();
                        replacement.push(get_qubit_from_bool(val));
                    } else if are_there_false_constants(vec![const_r, const_l]) {
                        replacement.push(QubitRef::from(Qubit::ConstFalse));
                    } else if are_there_true_constants(vec![const_l, const_r]) {
                        let control: QubitRef = if is_constant(l_qubit) {
                            // l_qubit must be true
                            r_qubit.clone()
                        } else {
                            // const_r must be true
                            l_qubit.clone()
                        };

                        let target: QubitRef = self.apply_mcx_gate(
                            &mut [control],
                            &None,
                            &mut gates_to_uncompute,
                            true,
                            true,
                        );
                        replacement.push(target);
                    } else {
                        // there are no constants
                        let target = self.apply_mcx_gate(
                            &mut [l_qubit.clone(), r_qubit.clone()],
                            &None,
                            &mut gates_to_uncompute,
                            true,
                            true,
                        );

                        assert!(gates_to_uncompute.is_empty());
                        replacement.push(target);
                    }
                }
                assert!(replacement.len() == left_operand.len());
                assert!(gates_to_uncompute.is_empty());
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Ext { from, value, .. } => {
                let mut replacement: Vec<QubitRef> = self.process(value);
                assert!(replacement.len() == from.bitsize());
                for _ in 0..(self.word_size - from.bitsize()) {
                    replacement.push(QubitRef::from(Qubit::ConstFalse));
                }
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Eq {
                left, right, nid, ..
            } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                assert!(self.is_rom(&left_operand));
                assert!(self.is_rom(&right_operand));
                let mut gates_to_uncompute = Vec::new();
                let mut replacement = self.eq(
                    &left_operand,
                    &right_operand,
                    nid,
                    "".to_string(),
                    &mut gates_to_uncompute,
                    true,
                    true,
                );
                assert!(self.is_rom(&replacement));
                replacement = self.get_safe_uncomputable_rom(&gates_to_uncompute, &replacement);
                self.uncompute(&gates_to_uncompute);
                // assert!(self.used_ancillas.is_empty());

                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Add { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                assert!(self.is_rom(&left_operand));
                assert!(self.is_rom(&right_operand));

                let mut gates_to_uncompute = Vec::new();
                let replacement =
                    self.add(&left_operand, &right_operand, &mut gates_to_uncompute, true);
                self.uncompute(&gates_to_uncompute);
                assert!(self.is_rom(&replacement));
                // assert!(self.used_ancillas.is_empty());
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Ite {
                cond, left, right, ..
            } => {
                let cond_operand = self.process(cond);
                assert!(self.is_rom(&cond_operand));
                assert!(cond_operand.len() == 1);
                let mut replacement: Vec<QubitRef>;
                if let Some(cond_val) = get_constant(&cond_operand[0]) {
                    if cond_val {
                        replacement = self.process(left);
                        assert!(self.is_rom(&replacement));
                    } else {
                        replacement = self.process(right);
                        assert!(self.is_rom(&replacement));
                    }
                } else {
                    let mut gates_to_uncompute = Vec::new();
                    replacement = Vec::new();
                    let left_operand = self.process(left);
                    let right_operand = self.process(right);
                    assert!(self.is_rom(&left_operand));
                    assert!(self.is_rom(&right_operand));
                    for (_i, (l_qubit, r_qubit)) in
                        left_operand.iter().zip(right_operand.iter()).enumerate()
                    {
                        let const_l = get_constant(l_qubit);
                        let const_r = get_constant(r_qubit);

                        if are_both_constants(const_l, const_r) {
                            if const_l.unwrap() == const_r.unwrap() {
                                replacement.push(l_qubit.clone());
                            } else if const_l.unwrap() {
                                // true-part is true
                                replacement.push(cond_operand[0].clone());
                            } else {
                                // true-part is false and false-part is true
                                let mut target = self.apply_mcx_gate(
                                    &mut [cond_operand[0].clone()],
                                    &None,
                                    &mut gates_to_uncompute,
                                    true,
                                    false,
                                );
                                target = self.add_not_gate(&mut target, None);
                                replacement.push(target.clone());
                            }
                        } else if are_there_false_constants(vec![const_l, const_r]) {
                            let target: QubitRef = if is_constant(l_qubit) {
                                assert!(!is_constant(&cond_operand[0]));
                                assert!(!is_constant(r_qubit));

                                self.add_not_gate(&mut cond_operand[0].clone(), None);
                                let t = self.apply_mcx_gate(
                                    &mut [cond_operand[0].clone(), r_qubit.clone()],
                                    &None,
                                    &mut gates_to_uncompute,
                                    true,
                                    false,
                                );
                                self.add_not_gate(&mut cond_operand[0].clone(), None);
                                t
                            } else {
                                assert!(!is_constant(&cond_operand[0]));
                                assert!(!is_constant(l_qubit));
                                self.apply_mcx_gate(
                                    &mut [cond_operand[0].clone(), l_qubit.clone()],
                                    &None,
                                    &mut gates_to_uncompute,
                                    true,
                                    true,
                                )
                            };
                            replacement.push(target);
                        } else {
                            // TODO: Optimize when there is only one constant and its true?
                            assert!(!is_constant(&cond_operand[0]));

                            // no constants
                            let mut target: QubitRef = self.apply_mcx_gate(
                                &mut [cond_operand[0].clone(), l_qubit.clone()],
                                &None,
                                &mut gates_to_uncompute,
                                true,
                                false,
                            );

                            self.add_not_gate(&mut cond_operand[0].clone(), None);

                            target = self.apply_mcx_gate(
                                &mut [cond_operand[0].clone(), r_qubit.clone()],
                                &Some(target),
                                &mut gates_to_uncompute,
                                true,
                                false,
                            );

                            self.add_not_gate(&mut cond_operand[0].clone(), None);
                            replacement.push(target.clone());
                        }
                    }
                    assert!(replacement.len() == left_operand.len());
                    assert!(gates_to_uncompute.is_empty());
                }
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Sub { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                assert!(self.is_rom(&left_operand));
                assert!(self.is_rom(&right_operand));
                let mut gates_to_uncompute = Vec::new();
                let replacement =
                    self.sub(&left_operand, &right_operand, &mut gates_to_uncompute, true);
                self.uncompute(&gates_to_uncompute);
                // assert!(self.used_ancillas.is_empty());
                assert!(self.is_rom(&replacement));
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Ult { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                assert!(left_operand.len() == right_operand.len());
                assert!(self.is_rom(&left_operand));
                assert!(self.is_rom(&right_operand));
                let mut gates_to_uncompute = Vec::new();
                let result = self.ult(
                    &left_operand,
                    &right_operand,
                    &false,
                    &mut gates_to_uncompute,
                    true,
                );
                assert!(result.len() == left_operand.len() + 1);
                let replacement = vec![result[result.len() - 1].clone()];
                assert!(self.is_rom(&replacement));
                self.uncompute(&gates_to_uncompute);
                // assert!(self.used_ancillas.is_empty());
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Mul { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                assert!(self.is_rom(&left_operand));
                assert!(self.is_rom(&right_operand));
                let mut gates_to_uncompute = Vec::new();
                let mut replacement =
                    self.mul(&left_operand, &right_operand, &mut gates_to_uncompute, true);
                assert!(self.is_rom(&replacement));
                replacement = self.get_safe_uncomputable_rom(&gates_to_uncompute, &replacement);
                self.uncompute(&gates_to_uncompute);
                // assert!(self.used_ancillas.is_empty());
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Div {
                left, right, nid, ..
            } => {
                let (replacement, _) = self.div(left, right, nid);
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Rem {
                left, right, nid, ..
            } => {
                let (_, replacement) = self.div(left, right, nid);
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Next { state, next, .. } => {
                let _ = self.process(state);
                self.circuit_stack.push(UnitaryRef::from(Unitary::Barrier));
                let replacement = self.process(next);
                assert!(self.is_rom(&replacement));
                self.record_mapping(state, self.current_n, replacement)
                // }
            }
            Node::Read { .. } | Node::Write { .. } => {
                unimplemented!()
            }
            _ => {
                panic!("Unknown BTOR2 node!");
            }
        }
    }

    pub fn process_model(&mut self, unroll_depth: usize) -> Result<()> {
        assert!(self.bad_state_qubits.is_empty());
        assert!(self.bad_state_nodes.is_empty());
        assert!(self.input_qubits.is_empty());
        assert!(self.circuit_stack.is_empty());
        assert!(self.word_size == 64 || self.word_size == 32);
        for i in 1..(unroll_depth + 1) {
            self.current_n = i as i32;
            for sequential in &self.model.sequentials {
                if let Node::Next { .. } = &*sequential.borrow() {
                    let _ = self.process(sequential);
                } else {
                    panic!("expecting 'Next' node here");
                }
            }
            for bad_state in &self.model.bad_states_initial {
                let bitblasted_bad_state = self.process(bad_state);
                assert!(bitblasted_bad_state.len() == 1);
                if let Some(val) = get_constant(&bitblasted_bad_state[0]) {
                    if val {
                        println!(
                            "Bad state found at state transition {} ({})",
                            i,
                            get_nid(bad_state)
                        );
                        self.result_ored_bad_states = QubitRef::from(Qubit::ConstTrue);
                        break;
                    }
                } else {
                    self.bad_state_qubits.push(bitblasted_bad_state[0].clone());
                }
            }

            for bad_state in &self.model.bad_states_sequential {
                let bitblasted_bad_state = self.process(bad_state);
                assert!(bitblasted_bad_state.len() == 1);
                if let Some(val) = get_constant(&bitblasted_bad_state[0]) {
                    if val {
                        println!(
                            "Bad state found at state transition {} ({})",
                            i,
                            get_nid(bad_state)
                        );
                        self.result_ored_bad_states = QubitRef::from(Qubit::ConstTrue);
                        break;
                    }
                } else {
                    self.bad_state_qubits.push(bitblasted_bad_state[0].clone());
                }
            }
        }

        if self.bad_state_qubits.is_empty() && !is_constant(&self.result_ored_bad_states) {
            self.result_ored_bad_states = QubitRef::from(Qubit::ConstFalse);
        }

        if !is_constant(&self.result_ored_bad_states) {
            let (val, bad_state_qubits) =
                prepare_controls_for_mcx(&self.bad_state_qubits, &self.result_ored_bad_states);

            if let Some(v) = val {
                self.result_ored_bad_states = get_qubit_from_bool(v);
            } else if bad_state_qubits.is_empty() {
                self.result_ored_bad_states = QubitRef::from(Qubit::ConstFalse);
                self.output_oracle = Some(QubitRef::from(Qubit::ConstFalse));
            } else if bad_state_qubits.len() == 1 {
                self.result_ored_bad_states = self.bad_state_qubits[0].clone();
            } else {
                let temp_ored = self.result_ored_bad_states.clone();
                self.or_bad_state_qubits(bad_state_qubits, &temp_ored);
            }
        } else {
            println!(
                "OR of bad states has a constant value -> {}",
                get_constant(&self.result_ored_bad_states).unwrap()
            );
        }

        if self.constraints.is_empty() {
            self.output_oracle = Some(self.result_ored_bad_states.clone());
        } else if self.output_oracle.is_none() {
            let mut tmp_controls: Vec<QubitRef> = vec![];

            if let Some(val_ored_bad_states) = get_constant(&self.result_ored_bad_states) {
                assert!(val_ored_bad_states);
            } else {
                tmp_controls.push(self.result_ored_bad_states.clone());
            }
            for (key, value) in self.constraints.iter() {
                let qubit = &key.value;
                tmp_controls.push(qubit.clone());
                if !value {
                    if let Some(q_val) = get_constant(qubit) {
                        if q_val {
                            println!("the constraints are never met");
                        }
                    } else {
                        self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                            input: qubit.clone(),
                        }));
                    }
                }
            }
            let target = self.get_rom(None);
            let (val_oracle, controls) = prepare_controls_for_mcx(&tmp_controls, &target);
            if let Some(value) = val_oracle {
                self.output_oracle = Some(get_qubit_from_bool(value));
                if value {
                    println!("This oracle always evaluate to -> {}", value);
                }
            } else {
                self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                    controls,
                    target: target.clone(),
                }));
                self.output_oracle = Some(target);
            }
        }
        self.print_stats();
        Ok(())
    }

    pub fn _write_model<W>(&self, mut _out: W) -> Result<()>
    where
        W: Write,
    {
        println!("missing implementation to write model");
        Ok(())
    }

    pub fn _dump_assignments(&self, assignment: &HashMap<HashableQubitRef, bool>) -> Result<()> {
        let mut file = File::create("assignments.txt")?;
        file.write_all(b"nid,value\n")?;
        for (nid, _) in self.mapping_nids.iter() {
            if let Some(value) = self._get_value_from_nid(*nid, assignment) {
                let line = format!("{},{}\n", nid, value);
                file.write_all(line.as_bytes())?;
            }
        }
        Ok(())
    }

    // pub fn _debug_with_assignments(&self, unroll_depth: usize, assignments: &HashMap<HashableQubitRef, bool>, model: Model) {

    //     for timestep in 1..(unroll_depth+1) {
    //         for (nid, node) in self.mapping_nids.iter() {

    //             match *node.borrow() {

    //             }
    //         }
    //     }

    // }

    fn get_value_in_bin(&self, value_: i64, sort: usize) -> Vec<bool> {
        let mut value = value_;
        let mut answer: Vec<bool> = Vec::new();
        for _ in 0..sort {
            if value % 2 == 0 {
                answer.push(false);
            } else {
                answer.push(true);
            }
            value /= 2;
        }
        assert!(sort == answer.len());
        answer
    }

    pub fn try_solve_dependency(
        &self,
        assignments: &mut HashMap<HashableQubitRef, bool>,
        qubit: &QubitRef,
        dependecies_values: &mut HashSet<HashableDependencyRef>,
    ) {
        if let Qubit::QBit {
            dependency: Some(dep),
            ..
        } = &*qubit.borrow()
        {
            self.solve_dependency(dep.clone(), assignments, dependecies_values);
        }
    }
    pub fn evaluate_circuit(&self, assignments: &mut HashMap<HashableQubitRef, bool>) {
        let mut dependencies_values: HashSet<HashableDependencyRef> = HashSet::new();
        for gate in self.circuit_stack.iter() {
            match &*gate.borrow() {
                Unitary::Not { input } => {
                    self.try_solve_dependency(assignments, input, &mut dependencies_values);
                    let key = HashableQubitRef::from(input.clone());

                    if assignments.contains_key(&key) {
                        let value = *assignments.get(&key).unwrap();
                        assignments.insert(key, !value);
                    } else {
                        // qubits are initialized in 0. Therefore, NOT should set it to true.
                        assignments.insert(key, true);
                    }
                }
                Unitary::Cnot { control, target } => {
                    assert!(!is_constant(control));
                    assert!(!is_constant(target));
                    self.try_solve_dependency(assignments, control, &mut dependencies_values);
                    self.try_solve_dependency(assignments, target, &mut dependencies_values);

                    let control_key = HashableQubitRef::from(control.clone());
                    let target_key = HashableQubitRef::from(target.clone());

                    if let Some(control_value) = assignments.get(&control_key) {
                        if *control_value {
                            if let Some(target_value) = assignments.get(&target_key) {
                                if *target_value {
                                    assignments.insert(target_key, false);
                                } else {
                                    assignments.insert(target_key, true);
                                }
                            } else {
                                // target is initialized in 0, therefore we must flip it to 1
                                assignments.insert(target_key, true);
                            }
                        } else if assignments.get(&target_key).is_none() {
                            // if control is not true we just check if its in the assignments-dictionary, if not we add it
                            assignments.insert(target_key, false);
                        }
                    } else {
                        panic!("Control qubit does not has any value! There is a bug.");
                    }
                }
                Unitary::Mcx { controls, target } => {
                    assert!(!controls.is_empty());
                    self.try_solve_dependency(assignments, target, &mut dependencies_values);
                    let mut controls_and = true;
                    for control in controls {
                        self.try_solve_dependency(assignments, control, &mut dependencies_values);
                        let control_key = HashableQubitRef::from(control.clone());
                        if let Some(control_val) = assignments.get(&control_key) {
                            if !(*control_val) {
                                controls_and = false;
                                break;
                            }
                        } else {
                            panic!(
                                "There is a control in MCX that doesnt has a value. This is a bug {:?}", control
                            );
                        }
                    }
                    let target_key = HashableQubitRef::from(target.clone());

                    if controls_and {
                        if let Some(target_value) = assignments.get(&target_key) {
                            if *target_value {
                                assignments.insert(target_key, false);
                            } else {
                                assignments.insert(target_key, true);
                            }
                        } else {
                            assignments.insert(target_key, true);
                        }
                    } else if assignments.get(&target_key).is_none() {
                        // if control is not true we just check if its in the assignments-dictionary, if not we add it
                        assignments.insert(target_key, false);
                    }
                }
                Unitary::Barrier => {}
            }
        }
    }

    pub fn solve_dependency(
        &self,
        dependency: DependencyRef,
        assignments: &mut HashMap<HashableQubitRef, bool>,
        dependencies_values: &mut HashSet<HashableDependencyRef>,
    ) {
        let dep_key = HashableDependencyRef::from(dependency.clone());
        if !dependencies_values.contains(&dep_key) {
            let dep = dependency.as_ref().borrow();
            let operands = &dep.operands;
            let name = &dep.name;
            let operand1_value = get_word_value(&operands[0].clone(), assignments).unwrap();
            let operand2_value = get_word_value(&operands[1], assignments).unwrap();
            assert!(operands[0].len() == operands[1].len());
            let mut result;
            if operand2_value != 0 {
                if name == "div" {
                    result = operand1_value / operand2_value;
                } else {
                    assert!(name == "rem");

                    result = operand1_value % operand2_value;
                }
            } else {
                result = operand1_value;
            }

            let target = self.dependencies.get(&dep_key).unwrap();
            for qubit in target.iter() {
                let key = HashableQubitRef::from(qubit.clone());
                assignments.insert(key, (result % 2) == 1);
                result /= 2;
            }
            dependencies_values.insert(dep_key);
        }
    }

    pub fn evaluate_input(&self, values: &[i64]) -> (bool, HashMap<HashableQubitRef, bool>) {
        assert!(self.output_oracle.is_some());
        let mut assignments: HashMap<HashableQubitRef, bool> = HashMap::new();
        // if let Some(value) = get_constant(&self.output_oracle.clone().unwrap()) {
        //     return (value, assignments);
        // }

        for (input, value) in self.input_qubits.iter().zip(values.iter()) {
            let qubits = input.1.clone();
            let bin_value = self.get_value_in_bin(*value, qubits.len());

            for (qubit, bit) in qubits.iter().zip(bin_value.iter()) {
                let key = HashableQubitRef::from(qubit.clone());
                assignments.insert(key, *bit);
            }
        }

        self.evaluate_circuit(&mut assignments);
        if let Some(value) = get_constant(&self.output_oracle.clone().unwrap()) {
            (value, assignments)
        } else {
            let key = HashableQubitRef::from(self.output_oracle.as_ref().unwrap().clone());
            return (*assignments.get(&key).unwrap(), assignments);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::unicorn::builder::generate_model;
    use crate::unicorn::memory::replace_memory;
    use bytesize::ByteSize;
    use riscu::load_object_file;
    use std::path::Path;

    use super::*;
    use crate::parse_btor2_file;

    #[test]
    fn test_constants_funcs() {
        assert!(matches!(
            &*get_qubit_from_constant_bit(1).borrow(),
            Qubit::ConstTrue
        ));
        assert!(matches!(
            &*get_qubit_from_constant_bit(0).borrow(),
            Qubit::ConstFalse
        ));
        assert!(matches!(
            &*get_qubit_from_bool(true).borrow(),
            Qubit::ConstTrue
        ));
        assert!(matches!(
            &*get_qubit_from_bool(false).borrow(),
            Qubit::ConstFalse
        ));

        assert!(is_constant(&QubitRef::from(Qubit::ConstFalse)));

        assert!(is_constant(&QubitRef::from(Qubit::ConstTrue)));

        assert!(!is_constant(&QubitRef::from(Qubit::QBit {
            name: "some_name".to_string(),
            dependency: None,
            stack: VecDeque::new()
        })));

        assert!(get_constant(&QubitRef::from(Qubit::ConstTrue)).unwrap());

        assert!(!get_constant(&QubitRef::from(Qubit::ConstFalse)).unwrap());
        assert!(get_constant(&QubitRef::from(Qubit::QBit {
            name: "some_name".to_string(),
            dependency: None,
            stack: VecDeque::new()
        }))
        .is_none());

        assert!(are_both_constants(Some(true), Some(false)));
        assert!(are_both_constants(Some(true), Some(true)));
        assert!(are_both_constants(Some(false), Some(true)));
        assert!(are_both_constants(Some(false), Some(false)));
        assert!(!are_both_constants(None, Some(false)));
        assert!(!are_both_constants(None, None));
        assert!(!are_both_constants(Some(false), None));

        assert!(!are_there_false_constants(vec![]));
        assert!(!are_there_false_constants(vec![Some(true)]));
        assert!(!are_there_false_constants(vec![None, None]));
        assert!(are_there_false_constants(vec![Some(false)]));

        assert!(!are_there_true_constants(vec![]));
        assert!(are_there_true_constants(vec![Some(true)]));
        assert!(!are_there_true_constants(vec![None, None]));
        assert!(!are_there_true_constants(vec![Some(false)]));

        let sort = NodeType::Bit;
        let value = 1;
        let bitsize = sort.bitsize();
        assert!(bitsize == 1);

        let replacement = get_replacement_from_constant(&sort, value);
        assert!(value == 1);
        assert!(replacement.len() == bitsize);
        assert!(matches!(&*replacement[0].borrow(), Qubit::ConstTrue));
    }

    #[test]
    fn test_prepare_controls_for_mcx() {
        let supers_qubit1 = QubitRef::from(Qubit::QBit {
            name: "qubit1".to_string(),
            dependency: None,
            stack: VecDeque::new(),
        });

        let supers_qubit2 = QubitRef::from(Qubit::QBit {
            name: "qubit2".to_string(),
            dependency: None,
            stack: VecDeque::new(),
        });

        let const_false = QubitRef::from(Qubit::ConstFalse);

        let const_true = QubitRef::from(Qubit::ConstTrue);

        let (value, controls) =
            prepare_controls_for_mcx(&[const_false, supers_qubit1.clone()], &supers_qubit2);

        assert!(!value.unwrap());
        assert!(controls.is_empty());

        let (value2, controls2) =
            prepare_controls_for_mcx(&[const_true.clone(), const_true], &supers_qubit1);

        assert!(value2.unwrap());
        assert!(controls2.is_empty());

        let (value3, controls3) =
            prepare_controls_for_mcx(&[supers_qubit1.clone()], &supers_qubit1);

        assert!(value3.is_none());
        assert!(controls3.len() == 1);
    }

    #[test]
    fn eq_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/eq.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());

        let mut qc = QuantumCircuit::new(&model, 64);

        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        assert!(qc.evaluate_input(&[0, 0]).0);
        assert!(qc.evaluate_input(&[1, 1]).0);
        assert!(!qc.evaluate_input(&[0, 1]).0);
        assert!(!qc.evaluate_input(&[1, 0]).0);
    }

    #[test]
    fn eq8_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/eq8.btor2"));
        // // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                if i == j {
                    assert!(qc.evaluate_input(&[i, j]).0);
                } else {
                    assert!(!qc.evaluate_input(&[i, j]).0);
                }
            }
        }
    }

    #[test]
    fn eq82_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/eq82.btor2"));
        // // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            if i == 0 {
                assert!(qc.evaluate_input(&[i]).0);
            } else {
                assert!(!qc.evaluate_input(&[i]).0);
            }
        }
    }

    #[test]
    fn ult2_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/ult2.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            if i < 213 {
                assert!(qc.evaluate_input(&[i]).0);
            } else {
                assert!(!qc.evaluate_input(&[i]).0);
            }
        }
    }

    #[test]
    fn add_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/add.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                let result = (i + j) & 255;

                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                assert!(oracle_val);

                let circuit_value = qc._get_value_from_nid(4, &assignments);
                assert!(circuit_value.is_some());
                assert!(result == circuit_value.unwrap());
            }
        }
    }

    #[test]
    fn add2_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/add2.btor2"));
        // // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = (i + 10) & 255;

            let (oracle_val, assignments) = qc.evaluate_input(&[i]);
            assert!(oracle_val);

            let circuit_value = qc._get_value_from_nid(4, &assignments);
            assert!(circuit_value.is_some());
            assert!(result == circuit_value.unwrap());
        }
    }

    #[test]
    fn sub2_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/sub2.btor2"));
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = (255 - i) & 255;

            let (_oracle_val, assignments) = qc.evaluate_input(&[i]);
            // assert!(oracle_val);

            let circuit_value = qc._get_value_from_nid(4, &assignments);
            assert!(circuit_value.is_some());
            println!("{} {} {}", i, result, circuit_value.unwrap());
            assert!(result == circuit_value.unwrap());
        }
    }

    #[test]
    fn and_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/and.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                let result = i & j & 255;

                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                assert!(oracle_val);
                let circuit_value = qc._get_value_from_nid(4, &assignments);
                assert!(circuit_value.is_some());
                assert!(result == circuit_value.unwrap());
            }
        }
    }

    #[test]
    fn and2_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/and2.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = i & 241 & 255;

            let (oracle_val, assignments) = qc.evaluate_input(&[i]);
            assert!(oracle_val);
            let circuit_value = qc._get_value_from_nid(4, &assignments);
            assert!(circuit_value.is_some());
            println!("{} {}", i, circuit_value.unwrap());
            assert!(result == circuit_value.unwrap());
        }
    }

    #[test]
    fn twos_complement_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/sub.btor2"));
        let mut qc = QuantumCircuit::new(&model, 64);

        let mut assignments: HashMap<HashableQubitRef, bool> = HashMap::new();
        let mut const_qubitset: Vec<QubitRef> = vec![];
        for i in 0..8 {
            const_qubitset.push(QubitRef::from(Qubit::QBit {
                name: "temp".to_string(),
                dependency: None,
                stack: VecDeque::new(),
            }));
            let key = HashableQubitRef::from(const_qubitset[i].clone());
            assignments.insert(key, false);
        }
        const_qubitset.push(QubitRef::from(Qubit::ConstFalse));

        let (_gates, answer) = qc.twos_complement(&const_qubitset);
        qc.evaluate_circuit(&mut assignments);

        for item in answer.iter().take(9) {
            let key = HashableQubitRef::from(item.clone());
            let value = assignments.get(&key).unwrap();
            assert!(!value);
        }
    }

    #[test]
    fn test_const_add() {
        let model = parse_btor2_file(Path::new("examples/quarc/add.btor2"));
        let mut qc = QuantumCircuit::new(&model, 64);
        let mut gates_to_uncompute = Vec::new();
        let wordsize = 9;
        for i in 1..256 {
            for j in 0..256 {
                let result: i32 = (i + j) & (256 * 2 - 1);

                let left_operand = get_qubitset_from_constant(&(i as u64), &wordsize);
                let right_operand = get_qubitset_from_constant(&(j as u64), &wordsize);

                let res_qubitset =
                    qc.add(&left_operand, &right_operand, &mut gates_to_uncompute, true);

                let mut local_result = 0;
                let mut curr_power = 1;
                for qubit in res_qubitset.iter() {
                    if let Some(v) = get_constant(qubit) {
                        if v {
                            local_result += curr_power;
                        }
                    } else {
                        unreachable!();
                    }
                    curr_power <<= 1;
                }
                assert!(local_result == result);
            }
        }
    }

    #[test]
    fn test_const_sub() {
        let model = parse_btor2_file(Path::new("examples/quarc/sub.btor2"));
        let mut qc = QuantumCircuit::new(&model, 64);

        let wordsize = 9;
        for i in 0..256 {
            for j in 0..256 {
                let result: i32 = (i - j) & 511;

                let left_operand = get_qubitset_from_constant(&(i as u64), &wordsize);
                let right_operand = get_qubitset_from_constant(&(j as u64), &wordsize);

                let mut gates_to_uncompute = Vec::new();
                let res_qubitset =
                    qc.sub(&left_operand, &right_operand, &mut gates_to_uncompute, true);

                let mut local_result = 0;
                let mut curr_power = 1;
                for qubit in res_qubitset.iter() {
                    if let Some(v) = get_constant(qubit) {
                        if v {
                            local_result += curr_power;
                        }
                    } else {
                        unreachable!()
                    }
                    curr_power <<= 1;
                }
                // println!("{}-{}= {}, got {}.", i, j, result, local_result);
                assert!(local_result == result);
            }
        }
    }

    #[test]
    fn sub_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/sub.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                let result = (i - j) & 255;

                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                assert!(oracle_val);

                let circuit_value = qc._get_value_from_nid(4, &assignments);
                assert!(circuit_value.is_some());
                assert!(result == circuit_value.unwrap());
            }
        }
    }

    #[test]
    fn test_const_ult() {
        let model = parse_btor2_file(Path::new("examples/quarc/add.btor2"));
        let mut qc = QuantumCircuit::new(&model, 64);

        let wordsize = 8;
        let mut gates_to_uncompute = Vec::new();
        for i in 1..256 {
            for j in 0..256 {
                let result: bool = i < j;

                let left_operand = get_qubitset_from_constant(&(i as u64), &wordsize);
                let right_operand = get_qubitset_from_constant(&(j as u64), &wordsize);

                let res_qubitset = qc.ult(
                    &left_operand,
                    &right_operand,
                    &false,
                    &mut gates_to_uncompute,
                    true,
                );
                let ult_result = res_qubitset[res_qubitset.len() - 1].clone();
                // println!(
                //     "{}<{}={}, got {}.",
                //     i,
                //     j,
                //     result,
                //     get_constant(&ult_result).unwrap()
                // );
                assert!(get_constant(&ult_result).unwrap() == result);
            }
        }
    }

    #[test]
    fn ult_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/ult.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);
        for i in 0..256 {
            for j in 0..256 {
                let (oracle_val, _assignments) = qc.evaluate_input(&[i, j]);
                println!("{} {} -> {}", i, j, oracle_val);
                if i < j {
                    assert!(oracle_val);
                } else {
                    assert!(!oracle_val);
                }
            }
        }
    }

    #[test]
    fn ite_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/ite.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 3);
        for cond in 0..2 {
            for true_part in 0..256 {
                for false_part in 0..256 {
                    let (_oracle_val, assignments) =
                        qc.evaluate_input(&[cond, true_part, false_part]);
                    let circuit_value = qc._get_value_from_nid(10, &assignments).unwrap();
                    if cond == 1 {
                        assert!(circuit_value == true_part);
                    } else {
                        assert!(circuit_value == false_part);
                    }
                }
            }
        }
    }

    #[test]
    fn ite2_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/ite2.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);
        for cond in 0..2 {
            for i in 0..256 {
                let (_, assignments) = qc.evaluate_input(&[cond, i]);
                let circuit_value = qc._get_value_from_nid(4, &assignments).unwrap();
                if cond == 1 {
                    assert!(circuit_value == i);
                } else {
                    assert!(circuit_value == 0);
                }
            }
        }
    }

    #[test]
    fn not_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/not.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = !i & 255;

            let (oracle_val, assignments) = qc.evaluate_input(&[i]);
            println!("i: {}", i);
            let circuit_value = qc._get_value_from_nid(3, &assignments);
            assert!(circuit_value.is_some());
            assert!(result == circuit_value.unwrap());
            assert!(oracle_val);
        }
    }

    #[test]
    fn mul_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/mul.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                let result = (i * j) & 255;

                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                assert!(oracle_val);

                let circuit_value = qc._get_value_from_nid(4, &assignments);
                assert!(!circuit_value.is_none());
                assert!(result == circuit_value.unwrap());
            }
        }
    }

    #[test]
    fn mul2_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/mul2.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = (i * 3) & 255;

            let (oracle_val, assignments) = qc.evaluate_input(&[i]);
            assert!(oracle_val);

            let circuit_value = qc._get_value_from_nid(4, &assignments);
            assert!(circuit_value.is_some());
            // println!("{} {}", i, circuit_value.unwrap());
            println!("{} {}", result, circuit_value.unwrap());
            assert!(result == circuit_value.unwrap());
        }
    }

    #[test]
    fn div_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/div.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                let circuit_value = qc._get_value_from_nid(4, &assignments);
                if j != 0 {
                    let result = (i / j) & 255;
                    println!("{} {}", i, j);
                    // println!(
                    //     "{}/{} --> {} = {}, {}",
                    //     i,
                    //     j,
                    //     result,
                    //     circuit_value.unwrap(),
                    //     get_word_value(&qc.temp, &assignments).unwrap()
                    // );
                    assert!(oracle_val);
                    assert!(circuit_value.is_some());
                    assert!(result == circuit_value.unwrap());
                }
            }
        }
    }

    #[test]
    fn one_const_div_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/div2.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let (oracle_val, assignments) = qc.evaluate_input(&[i]);
            let circuit_value = qc._get_value_from_nid(4, &assignments);

            if i != 0 {
                // println!("rem {}", get_word_value(&qc.temp, &assignments).unwrap());
                let result = (i / 50) & 255;
                // println!("{}/50 = {},  got {}", i, result, circuit_value.unwrap());
                assert!(oracle_val);
                assert!(circuit_value.is_some());
                assert!(result == circuit_value.unwrap());
            }
            // else {
            //     assert!(!oracle_val)
            // }
        }
    }

    #[test]
    fn rem_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/rem.btor2"));
        // assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);
        for i in 0..256 {
            for j in 0..256 {
                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                let circuit_value = qc._get_value_from_nid(5, &assignments);
                if j != 0 {
                    let result = (i % j) & 255;
                    assert!(oracle_val);
                    assert!(circuit_value.is_some());
                    println!("{} {}, {} {}", i, j, result, circuit_value.unwrap());
                    assert!(result == circuit_value.unwrap());
                }
            }
        }
    }

    #[test]
    fn symbolic_experiments_no_dynamic_mem() -> Result<()> {
        let mut simple_assignment_bad_inputs: HashSet<i32> = HashSet::new();
        for i in 0..6 {
            simple_assignment_bad_inputs.insert(i);
        }
        for i in 49..256 {
            simple_assignment_bad_inputs.insert(i);
        }

        let mut all_inputs_bad: HashSet<i32> = HashSet::new();
        let mut all_inputs_bad_but_zero: HashSet<i32> = HashSet::new();
        for i in 0..256 {
            all_inputs_bad.insert(i);
            if i > 0 {
                all_inputs_bad_but_zero.insert(i);
            }
        }
        let paths_to_timesteps = HashMap::from([
            // ("division-by-zero-3-35.m", (86, HashSet::from([48]))),
            // ("memory-access-fail-1-35.m", (72, all_inputs_bad)),
            ("nested-if-else-1-35.m", (123, HashSet::from([49]))),
            ("nested-if-else-reverse-1-35.m", (122, HashSet::from([49]))),
            // ("return-from-loop-1-35.m", (105, HashSet::from([48]))), //
            // (
            //     "simple-assignment-1-35.m",
            //     (105, simple_assignment_bad_inputs),
            // ),
            // ("simple-if-else-1-35.m", (117, HashSet::from([49]))),
            // (
            //     "simple-if-else-reverse-1-35.m",
            //     (115, HashSet::from([49])),
            // ),
            // (
            //     "simple-if-without-else-1-35.m",
            //     (116, HashSet::from([49])),
            // ),
            // ("d.m", (84, all_inputs_bad_but_zero)),
        ]);

        for (file_name, data) in paths_to_timesteps.iter() {
            println!("current file: {}", *file_name);
            let mut path = "examples/selfie/".to_owned();
            path.push_str(file_name);
            let program = load_object_file(&path)?;
            let mut model = generate_model(&program, ByteSize::mib(1).as_u64(), 8, 120, &[])?;

            replace_memory(&mut model);
            let mut qc = QuantumCircuit::new(&model, 64);
            let _ = qc.process_model(data.0);
            for input_value in 0..256 {
                println!("input value {}", input_value);
                let mut input_values = vec![];
                for _ in 0..qc.input_qubits.len() {
                    input_values.push(input_value as i64);
                }
                let (oracle_val, _) = qc.evaluate_input(&input_values);
                if data.1.get(&input_value).is_some() {
                    // qc._dump_assignments(&assignments)?;
                    assert!(oracle_val);
                } else {
                    assert!(!oracle_val);
                }
            }
        }
        Ok(())
    }
}

use crate::unicorn::{get_nid, HashableNodeRef, Model, Nid, Node, NodeRef, NodeType};
use anyhow::Result;
use std::cell::RefCell;
use std::cmp::max;
use std::collections::{HashMap, HashSet};
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
pub enum Qubit {
    ConstTrue,
    ConstFalse,
    QBit {
        name: String,
        dependency: Option<DependencyRef>,
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

fn prepare_controls_for_mcx(
    controls: &[QubitRef],
    target: &QubitRef,
) -> (Option<bool>, Vec<QubitRef>) {
    let mut is_used: HashSet<HashableQubitRef> = HashSet::new();
    let target_key = HashableQubitRef::from(target.clone());
    is_used.insert(target_key);

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
        (Some(true), result)
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
    pub dm_index: usize,
    pub output_oracle: Option<QubitRef>,
    // pub temp: Vec<QubitRef>,
    word_size: usize,
    model: &'a Model, // BTOR2 model
    use_dynamic_memory: bool,
}

impl<'a> QuantumCircuit<'a> {
    pub fn new(model_: &'a Model, word_size_: usize, use_dynamic_memory_: bool) -> Self {
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
            dm_index: 0,
            circuit_stack: Vec::new(),
            current_state_nodes: HashMap::new(),
            model: model_,
            word_size: word_size_,
            count_multiqubit_gates: 0,
            current_n: 0,
            qubit_to_nid: HashMap::new(),
            // temp: Vec::new(),
            result_ored_bad_states: QubitRef::from(Qubit::QBit {
                name: "result_or".to_string(),
                dependency: None,
            }),
            use_dynamic_memory: use_dynamic_memory_,
            output_oracle: None,
        }
    }

    fn not_gate(&mut self, a_qubit: &QubitRef) -> QubitRef {
        if let Some(a_const) = get_constant(a_qubit) {
            if a_const {
                QubitRef::from(Qubit::ConstFalse)
            } else {
                QubitRef::from(Qubit::ConstTrue)
            }
        } else {
            //  since we dont know whether this qubit is going to be used later
            let target = self.get_memory(1)[0].clone();
            assert!(!is_constant(&target));
            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                input: target.clone(),
            }));
            self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                control: a_qubit.clone(),
                target: target.clone(),
            }));
            target
        }
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
                        Some(replacement.clone())
                    } else {
                        let node_hash = HashableNodeRef::from(node.clone());
                        let index = self.current_state_nodes[&node_hash];
                        Some(replacements[&index].clone())
                    }
                }
                Node::Next { .. } | Node::Bad { .. } => None,
                _ => {
                    let replacements = self.mapping.get(&key).unwrap();
                    if replacements.contains_key(&self.current_n) {
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

    fn uncompute(&mut self, current_replacement: Vec<QubitRef>) -> Vec<QubitRef> {
        let mut new_replacement: Vec<QubitRef> = vec![];

        // PERFORM SWAPS to start committing to memory
        self.circuit_stack
            .push(UnitaryRef::from(Unitary::Barrier {}));
        for qubit in current_replacement {
            match &*qubit.borrow() {
                Qubit::ConstTrue | Qubit::ConstFalse => {
                    new_replacement.push(qubit.clone());
                }
                Qubit::QBit { name, .. } => {
                    let mut owned_string: String = "unc_".to_string();
                    owned_string.push_str(name);
                    self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                        control: qubit.clone(),
                        target: QubitRef::from(Qubit::QBit {
                            name: owned_string,
                            dependency: None,
                        }),
                    }))
                }
            }
        }
        self.circuit_stack
            .push(UnitaryRef::from(Unitary::Barrier {}));

        // move to the part that we want to uncompute. I.e before the last 2 swaps
        let mut i: i64 = self.circuit_stack.len() as i64;
        let mut count_barriers = 0;

        while count_barriers < 2 {
            count_barriers += match *self.circuit_stack[i as usize].borrow() {
                Unitary::Barrier => 1,
                _ => 0,
            };
            i -= 1;
        }
        if i > -1 {
            if let Unitary::Barrier = *self.circuit_stack[i as usize].borrow() {
                panic!("barrier should not be here!")
            }
        }

        // begin uncomputing
        let mut is_end_loop = false;
        while !is_end_loop {
            let gate_ = match *self.circuit_stack[i as usize].borrow() {
                Unitary::Barrier => None,
                _ => Some(self.circuit_stack[i as usize].clone()),
            };

            if let Some(gate) = gate_ {
                self.circuit_stack.push(gate);
            } else {
                is_end_loop = true;
            }
            i -= 1;
        }

        new_replacement
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

    fn process_input(&mut self, sort: usize, node: &NodeRef, name: String) -> Vec<QubitRef> {
        if let Some(replacement) = self.get_last_qubitset(node) {
            replacement
        } else {
            let mut replacement: Vec<QubitRef> = Vec::new();
            for i in 0..sort {
                let name = format!("{}[bit={}]", name, i);
                replacement.push(QubitRef::from(Qubit::QBit {
                    name,
                    dependency: None,
                }));
            }
            self.input_qubits.push((node.clone(), replacement.clone()));
            assert!(replacement.len() == sort);
            self.record_mapping(node, self.current_n, replacement)
        }
    }

    fn get_memory(&mut self, n: usize) -> Vec<QubitRef> {
        assert!(n > 0);
        let mut available_space = self.dynamic_memory.len() - self.dm_index;

        while available_space < n {
            let name = format!("dm{}", self.dynamic_memory.len());
            self.dynamic_memory.push(QubitRef::from(Qubit::QBit {
                name,
                dependency: None,
            }));
            available_space += 1;
        }

        let mut replacement: Vec<QubitRef> = Vec::new();

        while replacement.len() < n {
            replacement.push(self.dynamic_memory[self.dm_index].clone());
            self.dm_index += 1;
        }

        replacement
    }

    fn add_one_qubitset(
        &mut self,
        qubitset: &[QubitRef],
        target_set: Vec<QubitRef>,
    ) -> Vec<QubitRef> {
        let mut result: Vec<QubitRef> = vec![];

        let sort = qubitset.len();
        assert!(target_set.len() == qubitset.len());

        for qubit in target_set.iter() {
            result.push(qubit.clone());
        }

        for index in 0..sort {
            for i in index..sort {
                let mut tmp_controls = result[index..((sort - 1 - i) + index)].to_vec();
                tmp_controls.push(qubitset[index].clone());
                let mut target = result[sort - 1 - i + index].clone();
                let (mcx_res, controls) = prepare_controls_for_mcx(&tmp_controls, &target);

                if let Some(mcx_val) = mcx_res {
                    if mcx_val {
                        if let Some(target_value) = get_constant(&target) {
                            if target_value {
                                result[sort - 1 - i + index] = QubitRef::from(Qubit::ConstFalse);
                            } else {
                                result[sort - 1 - i + index] = QubitRef::from(Qubit::ConstTrue);
                            }
                        } else {
                            assert!(!is_constant(&result[sort - 1 - i + index]));
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                input: result[sort - 1 - i + index].clone(),
                            }))
                        }
                    }
                } else {
                    if let Some(value) = get_constant(&target) {
                        target = self.get_memory(1)[0].clone();
                        if value {
                            assert!(!is_constant(&target));
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                input: target.clone(),
                            }));
                        }
                    }
                    result[sort - 1 - i + index] = target.clone();
                    self.circuit_stack
                        .push(UnitaryRef::from(Unitary::Mcx { controls, target }))
                }
            }
        }
        assert!(result.len() == sort);
        result
    }

    fn add(&mut self, left_operand: &[QubitRef], right_operand: &[QubitRef]) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let mut replacement: Vec<QubitRef> = vec![];

        for _ in 0..left_operand.len() {
            replacement.push(QubitRef::from(Qubit::ConstFalse));
        }
        replacement = self.add_one_qubitset(left_operand, replacement);
        replacement = self.add_one_qubitset(right_operand, replacement);
        assert!(replacement.len() == left_operand.len());
        replacement
    }

    fn sub(&mut self, left_operand: &[QubitRef], right_operand: &[QubitRef]) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let (to_uncompute, negated_right) = self.twos_complement(right_operand);

        let replacement = self.add(left_operand, &negated_right);

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
            let mut target = result1[sort - i - 1].clone();
            let tmp_controls = result1[..(sort - i - 1)].to_vec();
            let (mcx_res, controls) = prepare_controls_for_mcx(&tmp_controls, &target);

            if let Some(mcx_val) = mcx_res {
                if mcx_val {
                    if let Some(target_val) = get_constant(&target) {
                        if target_val {
                            result1[sort - i - 1] = QubitRef::from(Qubit::ConstFalse);
                        } else {
                            result1[sort - i - 1] = QubitRef::from(Qubit::ConstTrue);
                        }
                    } else {
                        assert!(!is_constant(&target));
                        gates_to_uncompute.push(UnitaryRef::from(Unitary::Not {
                            input: target.clone(),
                        }));
                        self.circuit_stack
                            .push(UnitaryRef::from(Unitary::Not { input: target }));
                    }
                }
            } else {
                if let Some(value) = get_constant(&target) {
                    target = self.get_memory(1)[0].clone();
                    if value {
                        assert!(!is_constant(&target));
                        self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                            input: target.clone(),
                        }));
                    }
                    result1[sort - i - 1] = target.clone();
                }

                gates_to_uncompute.push(UnitaryRef::from(Unitary::Mcx {
                    controls: controls.clone(),
                    target: target.clone(),
                }));
                self.circuit_stack
                    .push(UnitaryRef::from(Unitary::Mcx { controls, target }));
            }
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
        ancillas: &[QubitRef],
    ) -> (Vec<UnitaryRef>, Vec<QubitRef>) {
        let mut gates_to_uncompute: Vec<UnitaryRef> = Vec::new();
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
            (gates_to_uncompute, result)
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
                        // TODO: Is hard to determine reusable memory because just after this there is an addition that can also use dynamic memory
                        // used_memory += 1;
                        let target = ancillas[i].clone();
                        assert!(!is_constant(&word[i]));
                        assert!(!is_constant(bit));
                        result.push(target.clone());
                        gates_to_uncompute.push(UnitaryRef::from(Unitary::Mcx {
                            controls: vec![word[i].clone(), bit.clone()],
                            target: target.clone(),
                        }));
                        self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                            controls: vec![word[i].clone(), bit.clone()],
                            target,
                        }));
                    }
                    i += 1;
                }
            }
            assert!(result.len() == word.len());
            (gates_to_uncompute, result)
        }
    }

    fn mul(&mut self, left_operand: &[QubitRef], right_operand: &[QubitRef]) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let mut replacement: Vec<QubitRef> = Vec::new();
        let ancillas = &self.get_memory(left_operand.len());
        for _ in 0..left_operand.len() {
            replacement.push(QubitRef::from(Qubit::ConstFalse));
        }

        for (index, bit) in left_operand.iter().enumerate() {
            let (gates_to_uncompute, result) =
                self.multiply_word_by_bit(right_operand, bit, index, ancillas);

            replacement = self.add_one_qubitset(&result, replacement);

            // uncompute ancillas
            for gate in gates_to_uncompute.iter().rev() {
                self.circuit_stack.push(gate.clone());
            }
            // self.dm_index -= self.dm_index;
        }
        self.dm_index -= ancillas.len();
        assert!(replacement.len() == left_operand.len());
        replacement
    }

    fn eq(
        &mut self,
        left_operand: &[QubitRef],
        right_operand: &[QubitRef],
        nid: &Nid,
        prefix: String,
    ) -> Vec<QubitRef> {
        assert!(left_operand.len() == right_operand.len());
        let mut local_gates: Vec<UnitaryRef> = vec![];
        let mut used_qubits = 0;
        let mut controls: Vec<QubitRef> = vec![];
        for (_i, (l_qubit, r_qubit)) in left_operand.iter().zip(right_operand.iter()).enumerate() {
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

                let target: QubitRef = self.get_memory(1)[0].clone();

                // let target: QubitRef = if self.use_dynamic_memory {
                //     self.get_memory(1)[0].clone()
                // } else {
                //     let name = format!("{}{}_eq_{}", prefix, nid, self.current_n);
                //     QubitRef::from(Qubit::QBit {
                //         name,
                //         dependency: None,
                //     })
                // };
                controls.push(target.clone());
                assert!(!is_constant(&target));

                used_qubits += 1;
                local_gates.push(UnitaryRef::from(Unitary::Not {
                    input: target.clone(),
                }));
                local_gates.push(UnitaryRef::from(Unitary::Cnot {
                    control: control.clone(),
                    target: target.clone(),
                }));

                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                    input: target.clone(),
                }));
                self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                    control: control.clone(),
                    target,
                }));
            } else {
                // no constants
                // let target: QubitRef = if self.use_dynamic_memory {
                //     self.get_memory(1)[0].clone()
                // } else {
                //     let name = format!("{}{}_eq{}_{}", prefix, nid, i, self.current_n);
                //     QubitRef::from(Qubit::QBit {
                //         name,
                //         dependency: None,
                //     })
                // };

                let target: QubitRef = self.get_memory(1)[0].clone();
                used_qubits += 1;
                controls.push(target.clone());

                self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                    control: l_qubit.clone(),
                    target: target.clone(),
                }));
                self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                    control: r_qubit.clone(),
                    target: target.clone(),
                }));
                assert!(!is_constant(&target));
                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                    input: target.clone(),
                }));

                // local gates
                local_gates.push(UnitaryRef::from(Unitary::Cnot {
                    control: l_qubit.clone(),
                    target: target.clone(),
                }));
                local_gates.push(UnitaryRef::from(Unitary::Cnot {
                    control: r_qubit.clone(),
                    target: target.clone(),
                }));
                local_gates.push(UnitaryRef::from(Unitary::Not { input: target }));
            }
        }
        let replacement: Vec<QubitRef>;
        let name = format!("{}{}_eqres_{}", prefix, nid, self.current_n);
        let tmp = prepare_controls_for_mcx(
            &controls,
            &QubitRef::from(Qubit::QBit {
                name: name.clone(),
                dependency: None,
            }),
        );
        controls = tmp.1;
        if let Some(value) = tmp.0 {
            replacement = vec![get_qubit_from_bool(value)];
        } else {
            let target: QubitRef = if self.use_dynamic_memory {
                self.get_memory(1)[0].clone()
            } else {
                QubitRef::from(Qubit::QBit {
                    name,
                    dependency: None,
                })
            };

            replacement = vec![target.clone()];
            self.circuit_stack
                .push(UnitaryRef::from(Unitary::Mcx { controls, target }));
        }
        self.dm_index -= used_qubits;
        for gate in local_gates.iter().rev() {
            self.circuit_stack.push(gate.clone());
        }

        assert!(replacement.len() == 1);
        replacement
    }

    fn _insert_into_contrants(&mut self, qubit: &QubitRef, value: bool) {
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

        assert!(left_operand.len() == right_operand.len());

        if are_all_constants(&left_operand) && are_all_constants(&right_operand) {
            let value_left = get_value_from_constants(&left_operand);
            let value_right = get_value_from_constants(&right_operand);

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
                }));
                r.push(QubitRef::from(Qubit::QBit {
                    name: format!("{}_rem{}_{}", nid, i, self.current_n),
                    dependency: Some(rem_dep.clone()),
                }));
                i += 1;
            }

            let mut key = HashableDependencyRef::from(coeff_dep);
            self.dependencies.insert(key, c.clone());

            key = HashableDependencyRef::from(rem_dep);
            self.dependencies.insert(key, r.clone());

            let res_mul = self.mul(&right_operand, &c);
            let res_sum = self.add(&res_mul, &r);

            let res_eq = self.eq(&res_sum, &left_operand, nid, "div_eq".to_string());

            // let res_ult = self.ult(&r, &right_operand); // TODO: there is a bug here, it modifies r
            // self.temp = res_ult.clone();

            assert!(res_eq.len() == 1);

            // self.insert_into_contrants(&res_eq[0], true);
            // self.insert_into_contrants(&res_mul[sort - 1], false);
            // self.insert_into_contrants(&res_sum[sort - 1], false);
            // self.insert_into_contrants(&res_ult[res_ult.len()-1], true);
            // println!("res ult {:?}", res_ult);

            // right operand must be different than 0
            let mut dummy_zero: Vec<QubitRef> = Vec::new();

            for _ in 0..right_operand.len() {
                dummy_zero.push(QubitRef::from(Qubit::ConstFalse));
            }

            assert!(c.len() == r.len());
            assert!(c.len() == right_operand.len());
            let c_answer = c[..(sort - 1)].to_vec();
            let r_answer = r[..(sort - 1)].to_vec();
            assert!(c_answer.len() == r_answer.len());
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

    fn ult(&mut self, left: &[QubitRef], right: &[QubitRef]) -> Vec<QubitRef> {
        let mut left_operand = left.to_owned();
        let mut right_operand = right.to_owned();
        left_operand.push(QubitRef::from(Qubit::ConstFalse));
        right_operand.push(QubitRef::from(Qubit::ConstFalse));
        self.sub(&left_operand, &right_operand)
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
                self.record_mapping(node, 0, replacement)
            }
            Node::Not { value, .. } => {
                let bitvector = self.process(value);
                let mut replacement: Vec<QubitRef> = Vec::new();
                for bit in &bitvector {
                    replacement.push(self.not_gate(bit));
                }
                assert!(replacement.len() == bitvector.len());
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

                if self.use_dynamic_memory {
                    let new_replacement = self.uncompute(replacement);
                    self.dm_index = 0;
                    self.record_mapping(node, self.current_n, new_replacement)
                } else {
                    self.record_mapping(node, self.current_n, replacement)
                }
            }
            Node::And {
                left, right, nid, ..
            } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                let mut replacement: Vec<QubitRef> = vec![];
                assert!(left_operand.len() == right_operand.len());
                for (i, (l_qubit, r_qubit)) in
                    left_operand.iter().zip(right_operand.iter()).enumerate()
                {
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

                        // let target: QubitRef = if self.use_dynamic_memory {
                        //     self.get_memory(1)[0].clone()
                        // } else {
                        //     QubitRef::from(Qubit::QBit {
                        //         name: "and".to_string(),
                        //         dependency: None,
                        //     })
                        // };
                        // replacement.push(target.clone());
                        // self.circuit_stack
                        //     .push(UnitaryRef::from(Unitary::Cnot { control, target }));
                        replacement.push(control);
                    } else {
                        // there are no constants
                        let target: QubitRef;
                        if HashableQubitRef::from(l_qubit.clone())
                            != HashableQubitRef::from(r_qubit.clone())
                        {
                            if self.use_dynamic_memory {
                                target = self.get_memory(1)[0].clone();
                            } else {
                                target = QubitRef::from(Qubit::QBit {
                                    name: format!("{}_and{}_{}", nid, i, self.current_n),
                                    dependency: None,
                                });
                            }
                            assert!(!is_constant(l_qubit));
                            assert!(!is_constant(r_qubit));
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                                controls: vec![l_qubit.clone(), r_qubit.clone()],
                                target: target.clone(),
                            }))
                        } else {
                            target = l_qubit.clone();
                        }
                        replacement.push(target);
                    }
                }
                assert!(replacement.len() == left_operand.len());
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Ext { from, value, .. } => {
                let mut replacement: Vec<QubitRef> = self.process(value);
                assert!(replacement.len() == from.bitsize());
                for _ in 0..(self.word_size - from.bitsize()) {
                    replacement.push(QubitRef::from(Qubit::ConstFalse));
                }
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Eq {
                left, right, nid, ..
            } => {
                // println!("{:?}", left);
                // println!("{:?}", right);
                // println!("**************");
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                let replacement = self.eq(&left_operand, &right_operand, nid, "".to_string());
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Add { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);

                let replacement = self.add(&left_operand, &right_operand);
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Ite {
                cond,
                left,
                right,
                nid,
                ..
            } => {
                let cond_operand = self.process(cond);
                assert!(cond_operand.len() == 1);
                // println!("ite cond {:?}", cond_operand);
                let mut replacement: Vec<QubitRef>;
                if let Some(cond_val) = get_constant(&cond_operand[0]) {
                    if cond_val {
                        replacement = self.process(left);
                    } else {
                        replacement = self.process(right);
                    }
                } else {
                    replacement = Vec::new();
                    let left_operand = self.process(left);
                    let right_operand = self.process(right);

                    // println!("ite left {:?}", left_operand);
                    // println!("ite right {:?}", right_operand);
                    for (i, (l_qubit, r_qubit)) in
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
                                let target: QubitRef = if self.use_dynamic_memory {
                                    self.get_memory(1)[0].clone()
                                } else {
                                    QubitRef::from(Qubit::QBit {
                                        name: format!("{}_ite{}_{}", nid, i, self.current_n),
                                        dependency: None,
                                    })
                                };
                                // TODO: Maybe is not necesary to request memory here for target?
                                replacement.push(target.clone());
                                assert!(!is_constant(&target));
                                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                    input: cond_operand[0].clone(),
                                }));
                                self.circuit_stack.push(UnitaryRef::from(Unitary::Cnot {
                                    control: cond_operand[0].clone(),
                                    target,
                                }));

                                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                    input: cond_operand[0].clone(),
                                }));
                            }
                        } else if are_there_false_constants(vec![const_l, const_r]) {
                            let target: QubitRef = if self.use_dynamic_memory {
                                self.get_memory(1)[0].clone()
                            } else {
                                QubitRef::from(Qubit::QBit {
                                    name: "ancilla_ite".to_string(),
                                    dependency: None,
                                })
                            };
                            replacement.push(target.clone());
                            if is_constant(l_qubit) {
                                assert!(!is_constant(&cond_operand[0]));
                                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                    input: cond_operand[0].clone(),
                                }));
                                assert!(!is_constant(&cond_operand[0]));
                                assert!(!is_constant(r_qubit));
                                self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                                    controls: vec![cond_operand[0].clone(), r_qubit.clone()],
                                    target,
                                }));
                                self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                    input: cond_operand[0].clone(),
                                }));
                            } else {
                                assert!(!is_constant(&cond_operand[0]));
                                assert!(!is_constant(l_qubit));
                                self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                                    controls: vec![cond_operand[0].clone(), l_qubit.clone()],
                                    target,
                                }));
                            }
                        } else {
                            // TODO: Optimize when there is only one constant and its true?

                            // no constants
                            let target: QubitRef = if self.use_dynamic_memory {
                                self.get_memory(1)[0].clone()
                            } else {
                                QubitRef::from(Qubit::QBit {
                                    name: format!("{}_ite{}_{}", nid, i, self.current_n),
                                    dependency: None,
                                })
                            };
                            let (_, controls_true_part) = prepare_controls_for_mcx(
                                &[cond_operand[0].clone(), l_qubit.clone()],
                                &target,
                            );
                            replacement.push(target.clone());
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                                controls: controls_true_part.clone(),
                                target: target.clone(),
                            }));
                            assert!(!is_constant(&cond_operand[0]));
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                input: cond_operand[0].clone(),
                            }));

                            let (_, controls_false_part) = prepare_controls_for_mcx(
                                &[cond_operand[0].clone(), r_qubit.clone()],
                                &target,
                            );
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                                controls: controls_false_part,
                                target,
                            }));
                            self.circuit_stack.push(UnitaryRef::from(Unitary::Not {
                                input: cond_operand[0].clone(),
                            }));
                        }
                    }
                    // println!("ite replacement {:?}", replacement);
                    assert!(replacement.len() == left_operand.len());
                }
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Sub { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                // println!("sub left: {:?}", left_operand);
                // println!("sub right: {:?}", right_operand);
                let replacement = self.sub(&left_operand, &right_operand);
                // println!("sub replacement: {:?}", replacement);
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Ult { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);
                assert!(left_operand.len() == right_operand.len());
                let result = self.ult(&left_operand, &right_operand);
                assert!(result.len() == left_operand.len() + 1);
                let replacement = vec![result[result.len() - 1].clone()];
                // println!("ult left: {:?}", left_operand);
                // println!("ult right: {:?}", right_operand);
                // println!("ult repl: {:?}", replacement);
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::Mul { left, right, .. } => {
                let left_operand = self.process(left);
                let right_operand = self.process(right);

                let replacement = self.mul(&left_operand, &right_operand);

                // println!("mul left: {:?}", left_operand);
                // println!("mul right: {:?}", right_operand);
                // println!("mul repl: {:?}", replacement);

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
                if self.use_dynamic_memory {
                    let new_replacement = self.uncompute(replacement);
                    self.dm_index = 0;
                    self.record_mapping(node, self.current_n, new_replacement)
                } else {
                    self.record_mapping(state, self.current_n, replacement)
                }
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
                    }
                } else {
                    self.bad_state_qubits.push(bitblasted_bad_state[0].clone());
                }
            }
        }

        if self.bad_state_qubits.is_empty() && !is_constant(&self.result_ored_bad_states) {
            self.result_ored_bad_states = QubitRef::from(Qubit::ConstFalse);
        }
        self.print_stats();

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
            let target = QubitRef::from(Qubit::QBit {
                name: "oracle_out".to_string(),
                dependency: None,
            });
            let (val_oracle, controls) = prepare_controls_for_mcx(&tmp_controls, &target);
            if let Some(value) = val_oracle {
                self.output_oracle = Some(get_qubit_from_bool(value));
            } else {
                self.circuit_stack.push(UnitaryRef::from(Unitary::Mcx {
                    controls,
                    target: target.clone(),
                }));
                self.output_oracle = Some(target);
            }
        }

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
    ) {
        if let Qubit::QBit {
            dependency: Some(dep),
            ..
        } = &*qubit.borrow()
        {
            self.solve_dependency(dep.clone(), assignments);
        }
    }
    pub fn evaluate_circuit(&self, assignments: &mut HashMap<HashableQubitRef, bool>) {
        for gate in self.circuit_stack.iter() {
            match &*gate.borrow() {
                Unitary::Not { input } => {
                    self.try_solve_dependency(assignments, input);
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
                    self.try_solve_dependency(assignments, control);
                    self.try_solve_dependency(assignments, target);

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
                    self.try_solve_dependency(assignments, target);
                    let mut controls_and = true;
                    for control in controls {
                        self.try_solve_dependency(assignments, control);
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
    ) {
        let dep_key = HashableDependencyRef::from(dependency.clone());
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
            result = 0;
        }

        let target = self.dependencies.get(&dep_key).unwrap();
        for qubit in target.iter() {
            let key = HashableQubitRef::from(qubit.clone());
            assignments.insert(key, (result % 2) == 1);
            result /= 2;
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
            dependency: None
        })));

        assert!(get_constant(&QubitRef::from(Qubit::ConstTrue)).unwrap());

        assert!(!get_constant(&QubitRef::from(Qubit::ConstFalse)).unwrap());
        assert!(get_constant(&QubitRef::from(Qubit::QBit {
            name: "some_name".to_string(),
            dependency: None
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
        });

        let supers_qubit2 = QubitRef::from(Qubit::QBit {
            name: "qubit2".to_string(),
            dependency: None,
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

        assert!(value3.unwrap());
        assert!(controls3.is_empty());
    }

    #[test]
    fn eq_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/eq.btor2"));
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());

        let mut qc = QuantumCircuit::new(&model, 64, false);

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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        let mut qc = QuantumCircuit::new(&model, 64, false);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = (255 - i) & 255;

            let (_, assignments) = qc.evaluate_input(&[i]);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        let mut qc = QuantumCircuit::new(&model, 64, false);

        let mut assignments: HashMap<HashableQubitRef, bool> = HashMap::new();
        let mut const_qubitset: Vec<QubitRef> = vec![];
        for i in 0..8 {
            const_qubitset.push(QubitRef::from(Qubit::QBit {
                name: "temp".to_string(),
                dependency: None,
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
        let mut qc = QuantumCircuit::new(&model, 64, false);

        let wordsize = 9;
        for i in 1..256 {
            for j in 0..256 {
                let result: i32 = (i + j) & (256 * 2 - 1);

                let left_operand = get_qubitset_from_constant(&(i as u64), &wordsize);
                let right_operand = get_qubitset_from_constant(&(j as u64), &wordsize);

                let res_qubitset = qc.add(&left_operand, &right_operand);

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
        let mut qc = QuantumCircuit::new(&model, 64, false);

        let wordsize = 9;
        for i in 0..256 {
            for j in 0..256 {
                let result: i32 = (i - j) & 511;

                let left_operand = get_qubitset_from_constant(&(i as u64), &wordsize);
                let right_operand = get_qubitset_from_constant(&(j as u64), &wordsize);

                let res_qubitset = qc.sub(&left_operand, &right_operand);

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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        let mut qc = QuantumCircuit::new(&model, 64, false);

        let wordsize = 8;
        for i in 1..256 {
            for j in 0..256 {
                let result: bool = i < j;

                let left_operand = get_qubitset_from_constant(&(i as u64), &wordsize);
                let right_operand = get_qubitset_from_constant(&(j as u64), &wordsize);

                let res_qubitset = qc.ult(&left_operand, &right_operand);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.is_empty());
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 3);
        for cond in 0..2 {
            for true_part in 0..256 {
                for false_part in 0..256 {
                    let (_, assignments) = qc.evaluate_input(&[cond, true_part, false_part]);
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
        assert!(model.bad_states_initial.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = !i & 255;

            let (oracle_val, assignments) = qc.evaluate_input(&[i]);
            assert!(oracle_val);

            let circuit_value = qc._get_value_from_nid(3, &assignments);
            assert!(circuit_value.is_some());
            assert!(result == circuit_value.unwrap());
        }
    }

    #[test]
    fn mul_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/mul.btor2"));
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                let result = (i * j) & 255;

                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                assert!(oracle_val);

                let circuit_value = qc._get_value_from_nid(4, &assignments);
                assert!(circuit_value.is_some());
                assert!(result == circuit_value.unwrap());
            }
        }
    }

    #[test]
    fn mul2_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/mul2.btor2"));
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 1);

        for i in 0..256 {
            let result = (i * 3) & 255;

            let (oracle_val, assignments) = qc.evaluate_input(&[i]);
            assert!(oracle_val);

            let circuit_value = qc._get_value_from_nid(4, &assignments);
            assert!(circuit_value.is_some());
            // println!("{} {}", i, circuit_value.unwrap());
            assert!(result == circuit_value.unwrap());
        }
    }

    #[test]
    fn div_test() {
        let model = parse_btor2_file(Path::new("examples/quarc/div.btor2"));
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);

        for i in 0..256 {
            for j in 0..256 {
                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                let circuit_value = qc._get_value_from_nid(4, &assignments);
                if j != 0 {
                    let result = (i / j) & 255;
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
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
        assert!(model.bad_states_initial.len() == 1);
        assert!(model.sequentials.len() == 1);
        let mut qc = QuantumCircuit::new(&model, 64, false);
        let _ = qc.process_model(1);
        assert!(qc.input_qubits.len() == 2);
        for i in 0..256 {
            for j in 0..256 {
                let (oracle_val, assignments) = qc.evaluate_input(&[i, j]);
                let circuit_value = qc._get_value_from_nid(4, &assignments);
                if j != 0 {
                    let result = (i % j) & 255;
                    assert!(oracle_val);
                    assert!(circuit_value.is_some());
                    // println!("{} {}, {} {}", i, j, result, circuit_value.unwrap());
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
            ("division-by-zero-3-35.m", (86, HashSet::from([48]))),
            ("memory-access-fail-1-35.m", (72, all_inputs_bad)),
            // ("nested-if-else-1-35.m", (123, HashSet::from([49]))),
            // (
            //     "nested-if-else-reverse-1-35.m",
            //     (122, HashSet::from([49])),
            // ),
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
            ("d.m", (84, all_inputs_bad_but_zero)),
        ]);

        for (file_name, data) in paths_to_timesteps.iter() {
            println!("current file: {}", *file_name);
            let mut path = "examples/selfie/".to_owned();
            path.push_str(file_name);
            let program = load_object_file(&path)?;
            let mut model = generate_model(&program, ByteSize::mib(1).as_u64(), 8, 120, &[])?;

            replace_memory(&mut model);
            let mut qc = QuantumCircuit::new(&model, 64, false);
            let _ = qc.process_model(data.0);
            for input_value in 0..256 {
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

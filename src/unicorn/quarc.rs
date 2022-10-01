use crate::unicorn::{HashableNodeRef, Model, Node, NodeRef, NodeType};
use anyhow::Result;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::rc::Rc;

//
// Public Interface
//

// BEGIN structs declaration
pub type UnitaryRef = Rc<RefCell<Unitary>>;

#[derive(Debug)]
pub enum Unitary {
    Not { input: QubitRef },
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
    QBit { name: String },
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

// END structs declaration

// BEGIN some functions

fn get_gate_from_constant_bit(bit: u64) -> QubitRef {
    assert!((bit == 0) | (bit == 1));
    if bit == 1 {
        QubitRef::from(Qubit::ConstTrue)
    } else {
        QubitRef::from(Qubit::ConstFalse)
    }
}

fn get_replacement_from_constant(sort: &NodeType, value_: u64) -> Vec<QubitRef> {
    let total_bits = sort.bitsize();
    let mut replacement: Vec<QubitRef> = Vec::new();
    let mut value = value_;
    for _ in 0..total_bits {
        replacement.push(get_gate_from_constant_bit(value % 2));
        value /= 2;
    }
    replacement
}

fn get_constant(gate_type: &QubitRef) -> Option<bool> {
    match &*gate_type.borrow() {
        Qubit::ConstFalse => Some(false),
        Qubit::ConstTrue => Some(true),
        _ => None,
    }
}
// END some functions

// Begin implementation

pub struct QuantumCircuit<'a> {
    pub bad_state_qubits: Vec<QubitRef>,
    pub bad_state_nodes: Vec<NodeRef>,
    pub all_qubits: HashSet<QubitRef>,
    pub constraints: HashMap<HashableQubitRef, bool>, // this is for remainder and division, these are constraint based.
    pub input_qubits: Vec<(NodeRef, Vec<QubitRef>)>,
    pub mapping: HashMap<HashableNodeRef, HashMap<usize, Vec<QubitRef>>>, // maps a btor2 operator to its resulting bitvector of gates
    pub circuit_stack: VecDeque<UnitaryRef>,
    pub count_multiqubit_gates: u64,
    pub current_n: usize,
    pub current_state_nodes: HashMap<HashableNodeRef, usize>,
    word_size: usize,
    model: &'a Model, // BTOR2 model
}

impl<'a> QuantumCircuit<'a> {
    pub fn new(model_: &'a Model, word_size_: usize) -> Self {
        Self {
            bad_state_qubits: Vec::new(),
            bad_state_nodes: Vec::new(),
            constraints: HashMap::new(),
            all_qubits: HashSet::new(),
            input_qubits: Vec::new(),
            mapping: HashMap::new(),
            circuit_stack: VecDeque::new(),
            current_state_nodes: HashMap::new(),
            model: model_,
            word_size: word_size_,
            count_multiqubit_gates: 0,
            current_n: 0,
        }
    }

    fn not_gate(&mut self, a_qubit: &QubitRef) -> QubitRef {
        let a = get_constant(a_qubit);

        if let Some(a_const) = a {
            if a_const {
                QubitRef::from(Qubit::ConstFalse)
            } else {
                QubitRef::from(Qubit::ConstTrue)
            }
        } else {
            self.circuit_stack.push_back(UnitaryRef::from(Unitary::Not {
                input: a_qubit.clone(),
            }));
            a_qubit.clone()
        }
    }

    fn get_last_qubitset(&mut self, node: &NodeRef) -> Option<Vec<QubitRef>> {
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
                Node::State { .. } => {
                    let replacements = self.mapping.get(&key).unwrap();
                    if let Some(replacement) = replacements.get(&(self.current_n - 1)) {
                        Some(replacement.clone())
                    } else {
                        let node_hash = HashableNodeRef::from(node.clone());
                        let index = self.current_state_nodes[&node_hash];
                        Some(replacements[&index].clone())
                    }
                }
                Node::Next { .. } => {
                    panic!("Trying to get last qubitset for Next, Sort, or Init is not possible");
                }
                _ => {
                    // Node::Input is included here?
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

    fn record_mapping(
        &mut self,
        node: &NodeRef,
        index: usize,
        replacement: Vec<QubitRef>,
    ) -> Vec<QubitRef> {
        let key = HashableNodeRef::from(node.clone());

        if !self.mapping.contains_key(&key) {
            self.mapping.insert(key.clone(), HashMap::new());
        }

        let replacements = self.mapping.get_mut(&key).unwrap();
        assert!(!replacements.contains_key(&index));
        replacements.insert(index, replacement.clone());
        replacement
    }

    fn process_input(&mut self, sort: usize, node: &NodeRef, name: String) -> Vec<QubitRef> {
        if let Some(replacement) = self.get_last_qubitset(node) {
            replacement
        } else {
            let mut replacement: Vec<QubitRef> = Vec::new();
            for i in 0..sort {
                let name = format!("{}[bit={}]", name, i);
                replacement.push(QubitRef::from(Qubit::QBit { name }));
            }
            self.input_qubits.push((node.clone(), replacement.clone()));
            assert!(replacement.len() == sort);
            self.record_mapping(node, self.current_n, replacement)
        }
    }

    fn process(&mut self, node: &NodeRef) -> Vec<QubitRef> {
        match &*node.borrow() {
            Node::Const { sort, imm, .. } => {
                if let Some(replacement) = self.get_last_qubitset(node) {
                    replacement
                } else {
                    assert!(self.current_n == 0);
                    let replacement = get_replacement_from_constant(sort, *imm);
                    assert!(replacement.len() == sort.bitsize());
                    self.record_mapping(node, self.current_n, replacement)
                }
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

                if let Some(replacement) = self.get_last_qubitset(node) {
                    replacement
                } else {
                    assert!(self.current_n == 0);
                    let mut replacement = Vec::new();
                    if let Some(value) = init {
                        replacement = self.process(value);
                    } else {
                        for _ in 0..sort.bitsize() {
                            replacement.push(QubitRef::from(Qubit::ConstFalse));
                        }
                    }
                    assert!(replacement.len() == sort.bitsize());
                    self.record_mapping(node, self.current_n, replacement)
                }
            }
            Node::Not { value, .. } => {
                if let Some(replacement) = self.get_last_qubitset(node) {
                    replacement
                } else {
                    let bitvector = self.process(value);
                    let mut replacement: Vec<QubitRef> = Vec::new();
                    for bit in &bitvector {
                        replacement.push(self.not_gate(bit));
                    }
                    assert!(replacement.len() == bitvector.len());
                    self.record_mapping(node, self.current_n, replacement)
                }
            }
            Node::Bad { cond, .. } => {
                let replacement = self.process(cond);
                assert!(replacement.len() == 1);
                self.record_mapping(node, self.current_n, replacement)
            }
            Node::And {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Ext { from, value, .. } => {
                if let Some(replacement) = self.get_last_qubitset(node) {
                    replacement
                } else {
                    let mut replacement: Vec<QubitRef> = self.process(value);
                    assert!(replacement.len() == from.bitsize());
                    for _ in 0..(self.word_size - from.bitsize()) {
                        replacement.push(QubitRef::from(Qubit::ConstFalse));
                    }
                    self.record_mapping(node, self.current_n, replacement)
                }
            }
            Node::Eq {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Add {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Ite {
                cond: _,
                left: _,
                right: _,
                ..
            } => {
                unimplemented!()
            }
            Node::Sub {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Ult {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Mul {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Div {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Rem {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Read {
                memory: _,
                address: _,
                ..
            } => {
                unimplemented!()
            }
            Node::Write {
                memory: _,
                address: _,
                value: _,
                ..
            } => {
                unimplemented!()
            }
            _ => {
                panic!("Unknown BTOR2 node!");
            }
        }
    }

    pub fn process_model<W>(mut self, out: W, unroll_depth: usize) -> Result<()>
    where
        W: Write,
    {
        assert!(self.bad_state_qubits.is_empty());
        assert!(self.bad_state_nodes.is_empty());
        assert!(self.input_qubits.is_empty());
        assert!(self.circuit_stack.is_empty());
        assert!(self.word_size == 64 || self.word_size == 32);

        for i in 0..unroll_depth {
            self.current_n = i;
            for sequential in &self.model.sequentials {
                if let Node::Next { .. } = &*sequential.borrow() {
                    let replacement = self.process(sequential);
                    self.record_mapping(sequential, self.current_n, replacement);
                    // TODO: flush memory, and reset ancillas
                } else {
                    panic!("expecting 'Next' node here");
                }
            }

            for bad_state in &self.model.bad_states_sequential {
                let bitblasted_bad_state = self.process(bad_state);
                assert!(bitblasted_bad_state.len() == 1);
                self.bad_state_qubits.push(bitblasted_bad_state[0].clone());
            }
        }
        self.write_model(out)
    }

    pub fn write_model<W>(self, mut _out: W) -> Result<()>
    where
        W: Write,
    {
        unimplemented!()
    }
}

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
    Not {
        input: QubitRef
    }
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
    pub mapping: HashMap<HashableNodeRef, Vec<QubitRef>>, // maps a btor2 operator to its resulting bitvector of gates
    pub circuit_stack: VecDeque<UnitaryRef>,
    pub count_multiqubit_gates: u64,
    _word_size: u64,
    model: &'a Model, // BTOR2 model
}

impl<'a> QuantumCircuit<'a> {
    pub fn new(model_: &'a Model, word_size_: u64) -> Self {
        Self {
            bad_state_qubits: Vec::new(),
            bad_state_nodes: Vec::new(),
            constraints: HashMap::new(),
            all_qubits: HashSet::new(),
            input_qubits: Vec::new(),
            mapping: HashMap::new(),
            circuit_stack: VecDeque::new(),
            model: model_,
            _word_size: word_size_,
            count_multiqubit_gates: 0,
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
            self.circuit_stack.push_back(UnitaryRef::from(Unitary::Not{input: a_qubit.clone()}));
            a_qubit.clone()
        }
    }

    fn visit(&mut self, node: &NodeRef) -> Vec<QubitRef> {
        let key = HashableNodeRef::from(node.clone());
        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned().unwrap()
        } else {
            assert!(!self.mapping.contains_key(&key));
            let replacement = self.process(node);
            assert!(self.mapping.contains_key(&key));
            replacement
        }
    }

    fn record_mapping(&mut self, node: &NodeRef, replacement: Vec<QubitRef>) -> Vec<QubitRef> {
        let key = HashableNodeRef::from(node.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement.clone());
        replacement
    }

    fn process(&mut self, node: &NodeRef) -> Vec<QubitRef> {
        match &*node.borrow() {
            Node::Const { sort, imm, .. } => {
                let replacement = get_replacement_from_constant(sort, *imm);
                assert!(replacement.len() == sort.bitsize());
                self.record_mapping(node, replacement)
            }
            Node::State {
                init: None,
                sort,
                name,
                ..
            } => {
                // this is an input
                let mut replacement: Vec<QubitRef> = Vec::new();
                let name = name.as_deref().unwrap_or("?");
                for i in 0..sort.bitsize() {
                    let name = format!("{}[bit={}]", name, i);
                    replacement.push(QubitRef::from(Qubit::QBit { name }));
                }
                self.input_qubits.push((node.clone(), replacement.clone()));
                assert!(replacement.len() == sort.bitsize());
                self.record_mapping(node, replacement)
            }
            Node::Input { sort, name, .. } => {
                let mut replacement: Vec<QubitRef> = Vec::new();
                for i in 0..sort.bitsize() {
                    let name = format!("{}[bit={}]", name, i);
                    replacement.push(QubitRef::from(Qubit::QBit { name }));
                }
                self.input_qubits.push((node.clone(), replacement.clone()));
                assert!(replacement.len() == sort.bitsize());
                self.record_mapping(node, replacement)
            }
            Node::State { sort, init, .. } => {
                // This is a normal state
                let mut replacement = Vec::new();
                if let Some(value) = init {
                    replacement = self.visit(value);
                } else {
                    for _ in 0..sort.bitsize() {
                        replacement.push(QubitRef::from(Qubit::ConstFalse));
                    }
                }
                assert!(replacement.len() == sort.bitsize());
                self.record_mapping(node, replacement)
            }
            Node::Not { value, .. } => {
                let bitvector = self.visit(value);
                let mut replacement: Vec<QubitRef> = Vec::new();
                for bit in &bitvector {
                    replacement.push(self.not_gate(bit));
                }
                assert!(replacement.len() == bitvector.len());
                self.record_mapping(node, replacement)
            }
            Node::Bad { cond, .. } => {
                let replacement = self.visit(cond);
                assert!(replacement.len() == 1);
                self.record_mapping(node, replacement)
            }
            Node::And {
                left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Ext { from, value, .. } => {
                let mut replacement: Vec<QubitRef> = self.visit(value);
                assert!(replacement.len() == from.bitsize());
                for _ in 0..(64 - from.bitsize()) {
                    replacement.push(QubitRef::from(Qubit::ConstFalse));
                }
                self.record_mapping(node, replacement)
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

    pub fn process_model<W>(mut self, out: W) -> Result<()>
    where
        W: Write,
    {
        assert!(self.bad_state_qubits.is_empty());
        assert!(self.bad_state_nodes.is_empty());
        assert!(self.input_qubits.is_empty());
        assert!(self.circuit_stack.is_empty());

        for node in &self.model.bad_states_initial {
            let bitblasted_bad_state = self.process(node);
            assert!(bitblasted_bad_state.len() == 1);
            self.bad_state_qubits.push(bitblasted_bad_state[0].clone());
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

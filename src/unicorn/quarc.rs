use crate::unicorn::{HashableNodeRef, Model, Node, NodeRef};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::collections::VecDeque;

//
// Public Interface
//

// BEGIN structs declaration
pub type UnitaryRef = Rc<RefCell<Unitary>>;

#[derive(Debug)]
pub enum Unitary {

}

#[derive(Debug)]
pub struct Qubit {
    pub name: u64,
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
    pub fn new (model_: &'a Model, word_size_: u64) -> Self{
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
            count_multiqubit_gates: 0
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
            Node::Const { sort: _, imm: _, .. } => {
                unimplemented!()
            }
            Node::State {
                init: None,
                sort: _,
                name: _,
                ..
            } => {
                unimplemented!()
            }
            Node::Input { sort: _, name: _, .. } => {
                unimplemented!()
            }
            Node::State { sort: _, init: _, .. } => {
                unimplemented!()
            }
            Node::Not { value: _, .. } => {
                unimplemented!()
            }
            Node::Bad { cond: _, .. } => {
                unimplemented!()
            }
            Node::And { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Ext { from: _, value: _, .. } => {
                unimplemented!()
            }
            Node::Eq { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Add { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Ite {
                cond: _, left: _, right: _, ..
            } => {
                unimplemented!()
            }
            Node::Sub { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Ult { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Mul { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Div { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Rem { left: _, right: _, .. } => {
                unimplemented!()
            }
            Node::Read {
                memory: _, address: _, ..
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
                panic!("this should not be happening!");
            }
        }
    }

    pub fn process_model(mut self) {
        assert!(self.bad_state_qubits.len() == 0);
        assert!(self.bad_state_nodes.len() == 0);
        assert!(self.input_qubits.len() == 0);
        assert!(self.circuit_stack.len() == 0);
        

        for node in &self.model.bad_states_initial {
            let bitblasted_bad_state = self.process(node);
            assert!(bitblasted_bad_state.len() == 1);
            self.bad_state_qubits.push(bitblasted_bad_state[0].clone());
        }

    }
}


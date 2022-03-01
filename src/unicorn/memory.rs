use crate::unicorn::{HashableNodeRef, Model, Node, NodeRef, NodeType};
use log::{debug, trace};
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::mem::size_of;
use std::rc::Rc;

//
// Public Interface
//

pub fn replace_memory(model: &mut Model) {
    debug!("Performing scalar replacement of all memory accesses in model ...");
    let virtual_addresses = enumerate_virtual_addresses(model);
    let mut memory_replacer = MemoryReplacer::new(virtual_addresses);
    for sequential in &model.sequentials {
        memory_replacer.visit(sequential);
    }
    for bad_state in &model.bad_states_initial {
        memory_replacer.visit(bad_state);
    }
    for bad_state in &model.bad_states_sequential {
        memory_replacer.visit(bad_state);
    }
    model
        .sequentials
        .retain(|s| !memory_replacer.check_for_memory_sequential(s));
    model
        .sequentials
        .append(&mut memory_replacer.new_sequentials);
}

//
// Private Implementation
//

type MemorySlice = [NodeRef];
type MemoryState = Vec<NodeRef>;

struct MemoryReplacer {
    marks: HashSet<HashableNodeRef>,
    mapping: HashMap<HashableNodeRef, NodeRef>,
    memory_states: HashMap<HashableNodeRef, MemoryState>,
    new_sequentials: Vec<NodeRef>,
    virtual_addresses: Vec<u64>,
}

fn enumerate_virtual_addresses(model: &Model) -> Vec<u64> {
    model
        .data_range
        .clone()
        .chain(model.heap_range.clone())
        .chain(model.stack_range.clone())
        .step_by(size_of::<u64>())
        .collect()
}

fn new_const(imm: u64) -> NodeRef {
    Rc::new(RefCell::new(Node::Const {
        nid: 0,
        sort: NodeType::Word,
        imm,
    }))
}

fn new_state(init: Option<&NodeRef>, name: String) -> NodeRef {
    Rc::new(RefCell::new(Node::State {
        nid: 0,
        sort: NodeType::Word,
        init: init.cloned(),
        name: Some(name),
    }))
}

fn new_ite(cond: &NodeRef, left: &NodeRef, right: &NodeRef) -> NodeRef {
    Rc::new(RefCell::new(Node::Ite {
        nid: 0,
        sort: NodeType::Word,
        cond: cond.clone(),
        left: left.clone(),
        right: right.clone(),
    }))
}

fn new_ite_cmp(value: &NodeRef, imm: u64, left: &NodeRef, right: &NodeRef) -> NodeRef {
    let imm_node = Rc::new(RefCell::new(Node::Const {
        nid: 0,
        sort: NodeType::Word,
        imm,
    }));
    let eq_node = Rc::new(RefCell::new(Node::Eq {
        nid: 0,
        left: value.clone(),
        right: imm_node,
    }));
    Rc::new(RefCell::new(Node::Ite {
        nid: 0,
        sort: NodeType::Word,
        cond: eq_node,
        left: left.clone(),
        right: right.clone(),
    }))
}

fn new_next(state: &NodeRef, next: &NodeRef) -> NodeRef {
    Rc::new(RefCell::new(Node::Next {
        nid: 0,
        sort: NodeType::Word,
        state: state.clone(),
        next: next.clone(),
    }))
}

impl MemoryReplacer {
    fn new(virtual_addresses: Vec<u64>) -> Self {
        Self {
            marks: HashSet::new(),
            mapping: HashMap::new(),
            memory_states: HashMap::new(),
            new_sequentials: Vec::new(),
            virtual_addresses,
        }
    }

    fn record_mapping(&mut self, node: &NodeRef, replacement: &NodeRef) {
        let key = HashableNodeRef::from(node.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement.clone());
    }

    fn record_memory_state(&mut self, node: &NodeRef, memory_state: MemoryState) {
        let key = HashableNodeRef::from(node.clone());
        assert!(!self.memory_states.contains_key(&key));
        self.memory_states.insert(key, memory_state);
    }

    fn retrieve_memory_state(&self, node: &NodeRef) -> &MemoryState {
        let key = HashableNodeRef::from(node.clone());
        self.memory_states.get(&key).expect("must exist")
    }

    fn visit(&mut self, node: &NodeRef) -> Option<NodeRef> {
        let key = HashableNodeRef::from(node.clone());
        if !self.marks.contains(&key) {
            let replacement = self.process(node);
            assert!(!self.mapping.contains_key(&key));
            if let Some(ref n) = replacement {
                self.record_mapping(node, n);
            }
            self.marks.insert(key);
            replacement
        } else {
            self.mapping.get(&key).cloned()
        }
    }

    fn handle_uninitialized(&self, name: &str) -> MemoryState {
        trace!("Handling (uninitialized) memory state for '{}' ...", name);
        let addresses = &self.virtual_addresses;
        addresses
            .iter()
            .map(|a| new_state(None, format!("{}[{}]", name, a)))
            .collect()
    }

    fn handle_initialized(&self, init: &MemorySlice, name: &str) -> MemoryState {
        trace!("Handling (initialized) memory state for '{}' ...", name);
        let addresses = &self.virtual_addresses;
        addresses
            .iter()
            .zip(init.iter())
            .map(|(a, i)| new_state(Some(i), format!("{}[{}]", name, a)))
            .collect()
    }

    fn handle_load(&self, mem: &MemorySlice, address: &NodeRef) -> NodeRef {
        trace!("Handling READ({:?}) node ...", RefCell::as_ptr(address));
        let addresses = &self.virtual_addresses;
        let dead = new_const(0xdeadbeefdeadbeef);
        addresses
            .iter()
            .zip(mem.iter())
            .rfold(dead, |acc, (a, x)| new_ite_cmp(address, *a as u64, x, &acc))
    }

    fn handle_store(&self, mem: &MemorySlice, address: &NodeRef, value: &NodeRef) -> MemoryState {
        trace!("Handling WRITE({:?}) node ...", RefCell::as_ptr(address));
        let addresses = &self.virtual_addresses;
        addresses
            .iter()
            .zip(mem.iter())
            .map(|(a, x)| new_ite_cmp(address, *a as u64, value, x))
            .collect()
    }

    fn handle_merge(&self, cond: &NodeRef, left: &MemorySlice, right: &MemorySlice) -> MemoryState {
        trace!("Handling memory state merge ...");
        left.iter()
            .zip(right.iter())
            .map(|(l, r)| new_ite(cond, l, r))
            .collect()
    }

    fn handle_sequential(&self, state: &MemorySlice, next: &MemorySlice) -> MemoryState {
        trace!("Handling memory state transition ...");
        state
            .iter()
            .zip(next.iter())
            .map(|(s, n)| new_next(s, n))
            .collect()
    }

    #[rustfmt::skip]
    fn process(&mut self, node: &NodeRef) -> Option<NodeRef> {
        match *node.borrow_mut() {
            Node::Const { .. } => None,
            Node::Read { ref mut memory, ref mut address, .. } => {
                if let Some(n) = self.visit(memory) { *memory = n }
                if let Some(n) = self.visit(address) { *address = n }
                let input_state = self.retrieve_memory_state(memory);
                Some(self.handle_load(input_state, address))
            }
            Node::Write { ref mut memory, ref mut address, ref mut value, .. } => {
                if let Some(n) = self.visit(memory) { *memory = n }
                if let Some(n) = self.visit(address) { *address = n }
                if let Some(n) = self.visit(value) { *value = n }
                let input_state = self.retrieve_memory_state(memory);
                let output_state = self.handle_store(input_state, address, value);
                self.record_memory_state(node, output_state);
                None
            }
            Node::Add { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Sub { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Mul { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Div { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Rem { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Ult { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Ext { ref mut value, .. } => {
                if let Some(n) = self.visit(value) { *value = n }
                None
            }
            Node::Ite { ref mut cond, ref mut left, ref mut right, sort: NodeType::Memory, .. } => {
                if let Some(n) = self.visit(cond) { *cond = n }
                if self.visit(left).is_some() { panic!("replaced ite-left") }
                if self.visit(right).is_some() { panic!("replaced ite-right") }
                let left_state = self.retrieve_memory_state(left);
                let right_state = self.retrieve_memory_state(right);
                let output_state = self.handle_merge(cond, left_state, right_state);
                self.record_memory_state(node, output_state);
                None
            }
            Node::Ite { ref mut cond, ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(cond) { *cond = n }
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Eq { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::And { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                None
            }
            Node::Not { ref mut value, .. } => {
                if let Some(n) = self.visit(value) { *value = n }
                None
            }
            Node::State { init: None, sort: NodeType::Memory, ref name, .. } => {
                let name = name.as_deref().unwrap_or("mem-uninit");
                let output_state = self.handle_uninitialized(name);
                self.record_memory_state(node, output_state);
                None
            }
            Node::State { init: Some(ref mut init), sort: NodeType::Memory, ref name, .. } => {
                if self.visit(init).is_some() { panic!("replaced init") }
                let init_state = self.retrieve_memory_state(init);
                let name = name.as_deref().unwrap_or("mem-init");
                let output_state = self.handle_initialized(init_state, name);
                self.record_memory_state(node, output_state);
                None
            }
            Node::State { init: None, .. } => None,
            Node::State { init: Some(ref mut init), .. } => {
                if let Some(n) = self.visit(init) { *init = n }
                None
            }
            Node::Next { ref state, ref mut next, sort: NodeType::Memory, .. } => {
                if self.visit(state).is_some() { panic!("replaced state") }
                if self.visit(next).is_some() { panic!("replaced next-value") }
                let init_state = self.retrieve_memory_state(state);
                let next_state = self.retrieve_memory_state(next);
                let mut output_state = self.handle_sequential(init_state, next_state);
                self.new_sequentials.append(&mut output_state);
                None
            }
            Node::Next { ref state, ref mut next, .. } => {
                if self.visit(state).is_some() { panic!("replaced state") }
                if let Some(n) = self.visit(next) { *next = n }
                None
            }
            Node::Input { .. } => None,
            Node::Bad { ref mut cond, .. } => {
                if let Some(n) = self.visit(cond) { *cond = n }
                None
            }
            Node::Comment(_) => panic!("cannot handle"),
        }
    }

    fn check_for_memory_sequential(&mut self, sequential: &NodeRef) -> bool {
        if let Node::Next { state, .. } = &*sequential.borrow() {
            if let Node::State { sort, name, .. } = &*state.borrow() {
                if let NodeType::Memory = sort {
                    debug!(
                        "Memory state '{}' was replaced, removing",
                        name.as_deref().unwrap_or("?")
                    );
                    return true;
                }
            } else {
                panic!("expecting 'State' node here");
            }
        } else {
            panic!("expecting 'Next' node here");
        }
        false
    }
}

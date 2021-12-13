use crate::modeler::unroller::HashableNodeRef; // TODO: Move to module.
use crate::modeler::{Model, Node, NodeRef, NodeType};
use log::{debug, trace};
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

//
// Public Interface
//

pub fn fold_constants(model: &mut Model) {
    let mut constant_folder = ConstantFolder::new();
    model
        .sequentials
        .retain(|s| !check_for_constant_sequential(s, &mut constant_folder));
    for sequential in &model.sequentials {
        constant_folder.visit(sequential);
    }
}

//
// Private Implementation
//

struct ConstantFolder {
    marks: HashSet<HashableNodeRef>,
    mapping: HashMap<HashableNodeRef, NodeRef>,
    const_false: NodeRef,
    const_true: NodeRef,
}

fn check_for_constant_sequential(
    sequential: &NodeRef,
    constant_folder: &mut ConstantFolder,
) -> bool {
    if let Node::Next { state, next, .. } = &*sequential.borrow() {
        if let Node::State { init, name, .. } = &*state.borrow() {
            if let Some(init) = init {
                if RefCell::as_ptr(state) == RefCell::as_ptr(next) {
                    debug!(
                        "Sequential state '{}' [{}] became trivial, removing",
                        name.as_ref().map_or("?", |s| &*s),
                        get_constant(init).map_or("X".to_string(), |i| i.to_string()),
                    );
                    constant_folder.pre_record_mapping(state, init);
                    return true;
                }
                if let Some(init_imm) = get_constant(init) {
                    if let Some(next_imm) = get_constant(next) {
                        if init_imm == next_imm {
                            debug!(
                                "Sequential state '{}' [{} -> {}] became constant, removing",
                                name.as_ref().map_or("?", |s| &*s),
                                init_imm,
                                next_imm
                            );
                            constant_folder.pre_record_mapping(state, init);
                            return true;
                        }
                    }
                }
            }
        } else {
            panic!("expecting 'State' node here");
        }
    } else {
        panic!("expecting 'Next' node here");
    }
    false
}

fn get_constant(node: &NodeRef) -> Option<u64> {
    if let Node::Const { imm, .. } = &*node.borrow() {
        Some(*imm)
    } else {
        None
    }
}

fn is_const_true(node: &NodeRef) -> bool {
    get_constant(node) == Some(1)
}

fn is_const_false(node: &NodeRef) -> bool {
    get_constant(node) == Some(0)
}

fn new_const_with_type(imm: u64, sort: NodeType) -> NodeRef {
    Rc::new(RefCell::new(Node::Const { nid: 0, sort, imm }))
}

fn new_const(imm: u64) -> NodeRef {
    new_const_with_type(imm, NodeType::Word)
}

impl ConstantFolder {
    fn new() -> Self {
        Self {
            marks: HashSet::new(),
            mapping: HashMap::new(),
            const_false: new_const_with_type(0, NodeType::Bit),
            const_true: new_const_with_type(1, NodeType::Bit),
        }
    }

    fn pre_record_mapping(&mut self, node: &NodeRef, replacement: &NodeRef) {
        let key = HashableNodeRef {
            value: node.clone(),
        };
        self.record_mapping(node, replacement);
        assert!(!self.marks.contains(&key));
        self.marks.insert(key);
    }

    fn record_mapping(&mut self, node: &NodeRef, replacement: &NodeRef) {
        let key = HashableNodeRef {
            value: node.clone(),
        };
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement.clone());
    }

    fn visit(&mut self, node: &NodeRef) -> Option<NodeRef> {
        let key = HashableNodeRef {
            value: node.clone(),
        };
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

    fn fold_arithmetic_binary<F>(
        &self,
        left: &NodeRef,
        right: &NodeRef,
        f: F,
        f_name: &str,
    ) -> Option<NodeRef>
    where
        F: FnOnce(u64, u64) -> u64,
    {
        if let Some(left_imm) = get_constant(left) {
            if let Some(right_imm) = get_constant(right) {
                let result_imm = f(left_imm, right_imm);
                trace!(
                    "Folding {}({:?}[{}],{:?}[{}]) -> {}",
                    f_name,
                    RefCell::as_ptr(left),
                    left_imm,
                    RefCell::as_ptr(right),
                    right_imm,
                    result_imm
                );
                return Some(new_const(result_imm));
            }
        }
        None
    }

    fn fold_add(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, u64::wrapping_add, "ADD")
    }

    fn fold_sub(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, u64::wrapping_sub, "SUB")
    }

    fn fold_rem(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, u64::wrapping_rem, "REM")
    }

    fn fold_eq(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        if RefCell::as_ptr(left) == RefCell::as_ptr(right) {
            trace!(
                "Folding EQ({:?},{:?}) -> T",
                RefCell::as_ptr(left),
                RefCell::as_ptr(right)
            );
            return Some(self.const_true.clone());
        }
        if let Some(left_imm) = get_constant(left) {
            if let Some(right_imm) = get_constant(right) {
                let result = left_imm == right_imm;
                trace!(
                    "Folding EQ({:?}[{}],{:?}[{}]) -> {}",
                    RefCell::as_ptr(left),
                    left_imm,
                    RefCell::as_ptr(right),
                    right_imm,
                    if result { "T" } else { "F" }
                );
                let result_node = if result {
                    &self.const_true
                } else {
                    &self.const_false
                };
                return Some(result_node.clone());
            }
        }
        None
    }

    fn fold_and(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        if is_const_false(left) {
            trace!("Folding AND({:?}[F],_) -> F", RefCell::as_ptr(left));
            return Some(self.const_false.clone());
        }
        if is_const_false(right) {
            trace!("Folding AND(_,{:?}[F]) -> F", RefCell::as_ptr(right));
            return Some(self.const_false.clone());
        }
        if is_const_true(left) && is_const_true(right) {
            trace!(
                "Folding AND({:?}[T],{:?}[T]) -> T",
                RefCell::as_ptr(left),
                RefCell::as_ptr(right)
            );
            return Some(self.const_true.clone());
        }
        None
    }

    fn fold_not(&self, value: &NodeRef) -> Option<NodeRef> {
        if is_const_true(value) {
            trace!("Folding NOT({:?}[T]) -> F", RefCell::as_ptr(value));
            return Some(self.const_false.clone());
        }
        if is_const_false(value) {
            trace!("Folding NOT({:?}[F]) -> T", RefCell::as_ptr(value));
            return Some(self.const_true.clone());
        }
        None
    }

    #[rustfmt::skip]
    fn process(&mut self, node: &NodeRef) -> Option<NodeRef> {
        match *node.borrow_mut() {
            // TODO: Remove and use global `false` constant.
            Node::Const { sort: NodeType::Bit, imm: 0, .. } => {
                Some(self.const_false.clone())
            }
            // TODO: Remove and use global `true` constant.
            Node::Const { sort: NodeType::Bit, imm: 1, .. } => {
                Some(self.const_true.clone())
            }
            Node::Const { .. } => None,
            Node::Read { ref mut memory, ref mut address, .. } => {
                if let Some(n) = self.visit(memory) { *memory = n }
                if let Some(n) = self.visit(address) { *address = n }
                // TODO: Implement store-to-load forwarding.
                None
            }
            Node::Write { ref mut memory, ref mut address, ref mut value, .. } => {
                if let Some(n) = self.visit(memory) { *memory = n }
                if let Some(n) = self.visit(address) { *address = n }
                if let Some(n) = self.visit(value) { *value = n }
                // TODO: Implement store-to-load forwarding.
                None
            }
            Node::Add { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_add(left, right)
            }
            Node::Sub { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_sub(left, right)
            }
            Node::Rem { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_rem(left, right)
            }
            Node::Ite { ref mut cond, ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(cond) { *cond = n }
                if is_const_true(cond) {
                    trace!("Short-circuiting ITE(T,x,_) -> x");
                    if let Some(n) = self.visit(left) { *left = n }
                    return Some(left.clone())
                }
                if is_const_false(cond) {
                    trace!("Short-circuiting ITE(F,_,x) -> x");
                    if let Some(n) = self.visit(right) { *right = n }
                    return Some(right.clone())
                }
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                // TODO: Implement common sub-expression elimination.
                None
            }
            Node::Eq { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_eq(left, right)
            }
            Node::And { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_and(left, right)
            }
            Node::Not { ref mut value, .. } => {
                if let Some(n) = self.visit(value) { *value = n }
                self.fold_not(value)
            }
            Node::State { init: None, .. } => None,
            Node::State { init: Some(ref mut init), .. } => {
                if let Some(n) = self.visit(init) { *init = n }
                None
            }
            Node::Next { ref state, ref mut next, .. } => {
                if self.visit(state).is_some() { panic!("replaced state") }
                if let Some(n) = self.visit(next) { *next = n }
                None
            }
            Node::Comment(_) => panic!("cannot fold"),
        }
    }
}

use crate::unicorn::solver::{Solution, Solver};
use crate::unicorn::{HashableNodeRef, Model, Node, NodeRef, NodeType};
use log::{debug, trace, warn};
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

//
// Public Interface
//

pub fn optimize_model<S: Solver>(model: &mut Model) {
    debug!("Optimizing model using '{}' SMT solver ...", S::name());
    let mut constant_folder = ConstantFolder::<S>::new();
    model
        .sequentials
        .retain(|s| constant_folder.should_retain_sequential(s));
    for sequential in &model.sequentials {
        constant_folder.visit(sequential);
    }
    model
        .bad_states_initial
        .retain(|s| constant_folder.should_retain_bad_state(s, true));
    model
        .bad_states_sequential
        .retain(|s| constant_folder.should_retain_bad_state(s, false));
}

//
// Private Implementation
//

struct ConstantFolder<S> {
    smt_solver: S,
    marks: HashSet<HashableNodeRef>,
    mapping: HashMap<HashableNodeRef, NodeRef>,
    const_false: NodeRef,
    const_true: NodeRef,
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

impl<S: Solver> ConstantFolder<S> {
    fn new() -> Self {
        Self {
            smt_solver: S::new(),
            marks: HashSet::new(),
            mapping: HashMap::new(),
            const_false: new_const_with_type(0, NodeType::Bit),
            const_true: new_const_with_type(1, NodeType::Bit),
        }
    }

    fn pre_record_mapping(&mut self, node: &NodeRef, replacement: &NodeRef) {
        let key = HashableNodeRef::from(node.clone());
        self.record_mapping(node, replacement);
        assert!(!self.marks.contains(&key));
        self.marks.insert(key);
    }

    fn record_mapping(&mut self, node: &NodeRef, replacement: &NodeRef) {
        let key = HashableNodeRef::from(node.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement.clone());
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

    fn solve_boolean_binary(
        &mut self,
        node: &NodeRef,
        left: &NodeRef,
        right: &NodeRef,
        f_name: &str,
    ) -> Option<NodeRef> {
        if self.smt_solver.is_always_true(node) {
            trace!(
                "Solved {}({:?},{:?}) -> T",
                f_name,
                RefCell::as_ptr(left),
                RefCell::as_ptr(right)
            );
            return Some(self.const_true.clone());
        }
        if self.smt_solver.is_always_false(node) {
            trace!(
                "Solved {}({:?},{:?}) -> F",
                f_name,
                RefCell::as_ptr(left),
                RefCell::as_ptr(right)
            );
            return Some(self.const_false.clone());
        }
        None
    }

    // SMT-LIB does not specify the result of remainder by zero, for BTOR we
    // take the largest unsigned integer that can be represented.
    fn btor_u64_rem(left: u64, right: u64) -> u64 {
        u64::checked_rem(left, right).unwrap_or(u64::MAX)
    }

    fn btor_u64_div(left: u64, right: u64) -> u64 {
        u64::checked_div(left, right).unwrap_or(u64::MAX)
    }

    fn fold_add(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, u64::wrapping_add, "ADD")
    }

    fn fold_sub(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, u64::wrapping_sub, "SUB")
    }

    fn fold_mul(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, u64::wrapping_mul, "MUL")
    }

    fn fold_div(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, Self::btor_u64_div, "DIV")
    }

    fn fold_rem(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.fold_arithmetic_binary(left, right, Self::btor_u64_rem, "REM")
    }

    fn fold_ult(&self, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        if let Some(left_imm) = get_constant(left) {
            if let Some(right_imm) = get_constant(right) {
                let result = left_imm < right_imm;
                trace!(
                    "Folding ULT({:?}[{}],{:?}[{}]) -> {}",
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

    fn solve_ult(&mut self, node: &NodeRef, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.solve_boolean_binary(node, left, right, "ULT")
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

    fn solve_eq(&mut self, node: &NodeRef, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.solve_boolean_binary(node, left, right, "EQ")
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
        if is_const_true(left) {
            trace!("Strength-reducing AND(T,x) -> x");
            return Some(right.clone());
        }
        if is_const_true(right) {
            trace!("Strength-reducing AND(x,T) -> x");
            return Some(left.clone());
        }
        None
    }

    fn solve_and(&mut self, node: &NodeRef, left: &NodeRef, right: &NodeRef) -> Option<NodeRef> {
        self.solve_boolean_binary(node, left, right, "AND")
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

    fn fold_ext(&self, value: &NodeRef) -> Option<NodeRef> {
        if let Some(value_imm) = get_constant(value) {
            return Some(new_const(value_imm));
        }
        None
    }

    fn solve_ite_bit(
        &mut self,
        node: &NodeRef,
        cond: &NodeRef,
        left: &NodeRef,
        right: &NodeRef,
    ) -> Option<NodeRef> {
        if let Some(x) = self.solve_boolean_binary(node, left, right, "ITE") {
            return Some(x);
        }
        if self.smt_solver.is_always_equal(node, cond) {
            trace!("Strength-reducing ITE(x,_,_) -> x");
            return Some(cond.clone());
        }
        None
    }

    fn solve_ite_word(
        &mut self,
        node: &NodeRef,
        _cond: &NodeRef,
        left: &NodeRef,
        right: &NodeRef,
    ) -> Option<NodeRef> {
        if self.smt_solver.is_always_equal(node, left) {
            trace!("Strength-reducing ITE(_,x,_) -> x");
            return Some(left.clone());
        }
        if self.smt_solver.is_always_equal(node, right) {
            trace!("Strength-reducing ITE(_,_,x) -> x");
            return Some(right.clone());
        }
        None
    }

    // TODO: The following implementation of store-to-load forwarding is not
    // linear, it is in O(n*m) where 'n' and 'm' are the number of load and
    // store instructions respectively. It can be improved with a time-stamped
    // hash-map representing the memory.
    fn find_in_memory(memory: &NodeRef, address_imm: u64) -> Option<NodeRef> {
        if let Node::Write {
            memory,
            address,
            value,
            ..
        } = &*memory.borrow()
        {
            if Some(address_imm) == get_constant(address) {
                return Some(value.clone());
            }
            return Self::find_in_memory(memory, address_imm);
        }
        None
    }

    fn fold_read(&self, memory: &NodeRef, address: &NodeRef) -> Option<NodeRef> {
        if let Some(address_imm) = get_constant(address) {
            if let Some(value) = Self::find_in_memory(memory, address_imm) {
                trace!(
                    "Folding READ({:?}[{}]) -> {:?}",
                    RefCell::as_ptr(address),
                    address_imm,
                    RefCell::as_ptr(&value),
                );
                return Some(value);
            }
        }
        None
    }

    #[rustfmt::skip]
    fn process_fold(&mut self, node: &NodeRef) -> Option<NodeRef> {
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
                self.fold_read(memory, address)
            }
            Node::Write { ref mut memory, ref mut address, ref mut value, .. } => {
                if let Some(n) = self.visit(memory) { *memory = n }
                if let Some(n) = self.visit(address) { *address = n }
                if let Some(n) = self.visit(value) { *value = n }
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
            Node::Mul { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_mul(left, right)
            }
            Node::Div { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_div(left, right)
            }
            Node::Rem { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_rem(left, right)
            }
            Node::Ult { ref mut left, ref mut right, .. } => {
                if let Some(n) = self.visit(left) { *left = n }
                if let Some(n) = self.visit(right) { *right = n }
                self.fold_ult(left, right)
            }
            Node::Ext { ref mut value, .. } => {
                if let Some(n) = self.visit(value) { *value = n }
                self.fold_ext(value)
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
            Node::Input { .. } => None,
            Node::Bad { ref mut cond, .. } => {
                if let Some(n) = self.visit(cond) { *cond = n }
                None
            }
            Node::Comment(_) => panic!("cannot fold"),
        }
    }

    #[rustfmt::skip]
    fn process_solve(&mut self, node: &NodeRef) -> Option<NodeRef> {
        match &*node.borrow() {
            Node::Ult { left, right, .. } => {
                self.solve_ult(node, left, right)
            }
            Node::Eq { left, right, .. } => {
                self.solve_eq(node, left, right)
            }
            Node::And { left, right, .. } => {
                self.solve_and(node, left, right)
            }
            Node::Ite { sort: NodeType::Bit, cond, left, right, .. } => {
                self.solve_ite_bit(node, cond, left, right)
            }
            Node::Ite { sort: NodeType::Word, cond, left, right, .. } => {
                self.solve_ite_word(node, cond, left, right)
            }
            _ => None
        }
    }

    fn process(&mut self, node: &NodeRef) -> Option<NodeRef> {
        // First try to constant-fold nodes and only invoke the SMT solver on
        // some specific boolean operations in case constant-folding fails.
        self.process_fold(node).or_else(|| self.process_solve(node))
    }

    fn should_retain_bad_state(&mut self, bad_state: &NodeRef, use_smt: bool) -> bool {
        self.visit(bad_state);
        if let Node::Bad { cond, name, .. } = &*bad_state.borrow() {
            if is_const_false(cond) {
                debug!(
                    "Bad state '{}' became unreachable, removing",
                    name.as_deref().unwrap_or("?")
                );
                return false;
            }
            if is_const_true(cond) {
                warn!(
                    "Bad state '{}' became statically reachable!",
                    name.as_deref().unwrap_or("?")
                );
                return true;
            }
            if use_smt {
                match self.smt_solver.solve(cond) {
                    Solution::Sat => {
                        warn!(
                            "Bad state '{}' is satisfiable!",
                            name.as_deref().unwrap_or("?")
                        );
                        return true;
                    }
                    Solution::Unsat => {
                        debug!(
                            "Bad state '{}' is unsatisfiable, removing",
                            name.as_deref().unwrap_or("?")
                        );
                        return false;
                    }
                    Solution::Timeout => (),
                }
            }
            true
        } else {
            panic!("expecting 'Bad' node here");
        }
    }

    fn should_retain_sequential(&mut self, sequential: &NodeRef) -> bool {
        if let Node::Next { state, next, .. } = &*sequential.borrow() {
            if let Node::State { init, name, .. } = &*state.borrow() {
                if let Some(init) = init {
                    if RefCell::as_ptr(state) == RefCell::as_ptr(next) {
                        debug!(
                            "Sequential state '{}' [{}] became trivial, removing",
                            name.as_deref().unwrap_or("?"),
                            get_constant(init).map_or("X".to_string(), |i| i.to_string()),
                        );
                        self.pre_record_mapping(state, init);
                        return false;
                    }
                    if let Some(init_imm) = get_constant(init) {
                        if let Some(next_imm) = get_constant(next) {
                            if init_imm == next_imm {
                                debug!(
                                    "Sequential state '{}' [{} -> {}] became constant, removing",
                                    name.as_deref().unwrap_or("?"),
                                    init_imm,
                                    next_imm
                                );
                                self.pre_record_mapping(state, init);
                                return false;
                            }
                        }
                    }
                }
                true
            } else {
                panic!("expecting 'State' node here");
            }
        } else {
            panic!("expecting 'Next' node here");
        }
    }
}

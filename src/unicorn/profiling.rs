use crate::unicorn::{HashableNodeRef, Node, NodeRef, NodeType};
use std::collections::HashSet;

//
// Public Interface
//

pub fn count_nodes(root: &NodeRef) {
    let mut nodes_counter = NodesCounter::new();
    nodes_counter.visit(root);
    nodes_counter.print_counters();
    nodes_counter.reset_counters();
}

//
// Private Implementation
//

struct NodesCounter {
    marks: HashSet<HashableNodeRef>,
    const_counter: usize,
    read_counter: usize,
    write_counter: usize,
    add_counter: usize,
    sub_counter: usize,
    mul_counter: usize,
    divu_counter: usize,
    div_counter: usize,
    rem_counter: usize,
    sll_counter: usize,
    srl_counter: usize,
    ult_counter: usize,
    ext_counter: usize,
    memory_ite_counter: usize,
    ite_counter: usize,
    eq_counter: usize,
    and_counter: usize,
    not_counter: usize,
    memory_state_counter: usize,
    state_counter: usize,
    input_counter: usize,
    bad_counter: usize,
    good_counter: usize,
    or_counter: usize,
    operator_counter: usize,
    nodes_counter: usize
}

impl NodesCounter {
    fn new() -> Self {
        Self {
            marks: HashSet::new(),
            const_counter: 0,
            read_counter: 0,
            write_counter: 0,
            add_counter: 0,
            sub_counter: 0,
            mul_counter: 0,
            divu_counter: 0,
            div_counter: 0,
            rem_counter: 0,
            sll_counter: 0,
            srl_counter: 0,
            ult_counter: 0,
            ext_counter: 0,
            memory_ite_counter: 0,
            ite_counter: 0,
            eq_counter: 0,
            and_counter: 0,
            not_counter: 0,
            memory_state_counter: 0,
            state_counter: 0,
            input_counter: 0,
            bad_counter: 0,
            good_counter: 0,
            or_counter: 0,
            operator_counter: 0,
            nodes_counter: 0
        }
    }

    fn const_inc(&mut self) { self.const_counter += 1; }
    fn read_inc(&mut self) { self.read_counter += 1; }
    fn write_inc(&mut self) { self.write_counter += 1; }
    fn add_inc(&mut self) { self.add_counter += 1; }
    fn sub_inc(&mut self) { self.sub_counter += 1; }
    fn mul_inc(&mut self) { self.mul_counter += 1; }
    fn divu_inc(&mut self) { self.divu_counter += 1; }
    fn div_inc(&mut self) { self.div_counter += 1; }
    fn rem_inc(&mut self) { self.rem_counter += 1; }
    fn sll_inc(&mut self) { self.sll_counter += 1; }
    fn srl_inc(&mut self) { self.srl_counter += 1; }
    fn ult_inc(&mut self) { self.ult_counter += 1; }
    fn ext_inc(&mut self) { self.ext_counter += 1; }
    fn memory_ite_inc(&mut self) { self.memory_ite_counter += 1; }
    fn ite_inc(&mut self) { self.ite_counter += 1; }
    fn eq_inc(&mut self) { self.eq_counter += 1; }
    fn and_inc(&mut self) { self.and_counter += 1; }
    fn not_inc(&mut self) { self.not_counter += 1; }
    fn memory_state_inc(&mut self) { self.memory_state_counter += 1; }
    fn state_inc(&mut self) { self.state_counter += 1; }
    fn input_inc(&mut self) { self.input_counter += 1; }
    fn bad_inc(&mut self) { self.bad_counter += 1; }
    fn good_inc(&mut self) { self.good_counter += 1; }
    fn or_inc(&mut self) { self.or_counter += 1; }
    fn operator_inc(&mut self) { self.operator_counter += 1; }
    fn nodes_inc(&mut self) { self.nodes_counter += 1; }

    fn reset_counters(&mut self) {
        self.const_counter = 0;
        self.read_counter = 0;
        self.write_counter = 0;
        self.add_counter = 0;
        self.sub_counter = 0;
        self.mul_counter = 0;
        self.divu_counter = 0;
        self.div_counter = 0;
        self.rem_counter = 0;
        self.sll_counter = 0;
        self.srl_counter = 0;
        self.ult_counter = 0;
        self.ext_counter = 0;
        self.memory_ite_counter = 0;
        self.ite_counter = 0;
        self.eq_counter = 0;
        self.and_counter = 0;
        self.not_counter = 0;
        self.memory_state_counter = 0;
        self.state_counter = 0;
        self.input_counter = 0;
        self.bad_counter = 0;
        self.good_counter = 0;
        self.or_counter = 0;
        self.operator_counter = 0;
        self.nodes_counter = 0;
    }

    fn print_counters(&mut self) {
        println!("{} nodes in total", self.nodes_counter);
        println!();
        println!("{} const nodes", self.const_counter);
        println!("{} input nodes", self.input_counter);
        println!("{} read nodes", self.read_counter);
        println!("{} write nodes", self.write_counter);
        println!("{} memory state nodes", self.memory_state_counter);
        println!("{} state nodes", self.state_counter);
        println!("{} bad state nodes", self.bad_counter);
        println!("{} good state nodes", self.good_counter);
        println!("{} operator nodes", self.operator_counter);
        println!("Including:");
        println!("  {} add nodes", self.add_counter);
        println!("  {} sub nodes", self.sub_counter);
        println!("  {} mul nodes", self.mul_counter);
        println!("  {} divu nodes", self.divu_counter);
        println!("  {} div nodes", self.div_counter);
        println!("  {} rem nodes", self.rem_counter);
        println!("  {} sll nodes", self.sll_counter);
        println!("  {} srl nodes", self.srl_counter);
        println!("  {} ult nodes", self.ult_counter);
        println!("  {} ext nodes", self.ext_counter);
        println!("  {} memory ite nodes", self.memory_ite_counter);
        println!("  {} ite nodes", self.ite_counter);
        println!("  {} eq nodes", self.eq_counter);
        println!("  {} and nodes", self.and_counter);
        println!("  {} not nodes", self.not_counter);
        println!("  {} or nodes", self.or_counter);
    }

    fn visit(&mut self, node: &NodeRef) {
        let key = HashableNodeRef::from(node.clone());
        if !self.marks.contains(&key) {
            self.process(node);
            self.marks.insert(key);
        }
    }

    #[rustfmt::skip]
    fn process(&mut self, node: &NodeRef) {
        match &*node.borrow() {
            Node::Const { sort, imm, .. } => {
                self.const_inc();
                self.nodes_inc();
            }
            Node::Read { memory, address, .. } => {
                self.visit(memory);
                self.visit(address);
                self.read_inc();
                self.nodes_inc();
            }
            Node::Write { memory, address, value, .. } => {
                self.visit(memory);
                self.visit(address);
                self.visit(value);
                self.write_inc();
                self.nodes_inc();
            }
            Node::Add { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.add_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Sub { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.sub_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Mul { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.mul_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Div { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.div_inc();
                self.operator_inc();
                self.nodes_inc();
            },
            Node::Rem { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.rem_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Ult { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.ult_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Ext { from, value, .. } => {
                self.visit(value);
                self.ext_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Ite { sort: NodeType::Memory, cond, left, right, .. } => {
                self.visit(cond);
                self.visit(left);
                self.visit(right);
                self.memory_ite_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Ite { sort, cond, left, right, .. } => {
                self.visit(cond);
                self.visit(left);
                self.visit(right);
                self.ite_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Eq { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.eq_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::And { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.and_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Or { left, right, .. } => {
                self.visit(left);
                self.visit(right);
                self.or_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::Not { value, .. } => {
                self.visit(value);
                self.not_inc();
                self.operator_inc();
                self.nodes_inc();
            }
            Node::State { sort: NodeType::Memory, name, init, .. } => {
                self.memory_state_inc();
                self.nodes_inc();
                match init {
                    Some(value) => {
                        self.visit(value);
                    }
                    None => {}
                }}
            Node::State { sort, name, init, .. } => {
                self.state_inc();
                self.nodes_inc();
                match init {
                    Some(value) => {
                        self.visit(value);
                    }
                    None => {}
                }
            }
            Node::Input { sort, name, .. } => {
                self.input_inc();
                self.nodes_inc();
            }
            Node::Next { .. } => panic!("should be unreachable"),
            Node::Bad { cond, .. } => {
                self.bad_inc();
                self.nodes_inc();
                self.visit(cond);
            },
            Node::Good { cond, .. } => {
                self.good_inc();
                self.nodes_inc();
                self.visit(cond);
            },
            Node::Comment(_) => panic!("should be unreachable"),
        }
    }
}

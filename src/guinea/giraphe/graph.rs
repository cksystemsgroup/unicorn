use std::default::Default;

use egui::Ui;
use indexmap::IndexMap;
use log::{debug, trace};
use riscu::Register;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Array, Bitvector, Boolean};
use crate::guinea::giraphe::{Giraphe, MachineWord, Spot, Value};
use crate::unicorn::{Model, Nid, Node, NodeRef, NodeType};

impl Giraphe {
    pub fn from(model: &Model) -> Self {
        assert!(
            !model.lines.is_empty(),
            "Can't convert model before it was renumbered!"
        );

        let mut roots = Vec::new();
        let mut states = Vec::new();
        let mut registers = Default::default();

        let mut node_lookup = IndexMap::new();
        let mut node_to_children = IndexMap::new();

        for noderef in &model.lines {
            let node = match &*noderef.borrow() {
                Node::Comment(c) => {
                    trace!("Skipping comment in model2graph conversion: {c}");
                    continue;
                }
                _ => Spot::from(noderef),
            };

            match &*noderef.borrow() {
                Node::Const { nid, .. } => {
                    node_lookup.insert(*nid, node);
                    node_to_children.entry(*nid).or_insert_with(Vec::new);
                }
                Node::Not { nid, value, .. } | Node::Ext { nid, value, .. } => {
                    node_lookup.insert(*nid, node);
                    let child = noderef_to_nid(value);
                    node_to_children
                        .entry(*nid)
                        .or_insert_with(Vec::new)
                        .append(&mut vec![child]);
                }
                Node::Read {
                    nid,
                    memory: left,
                    address: right,
                    ..
                }
                | Node::Add {
                    nid, left, right, ..
                }
                | Node::Sub {
                    nid, left, right, ..
                }
                | Node::Mul {
                    nid, left, right, ..
                }
                | Node::Div {
                    nid, left, right, ..
                }
                | Node::Rem {
                    nid, left, right, ..
                }
                | Node::Sll {
                    nid, left, right, ..
                }
                | Node::Srl {
                    nid, left, right, ..
                }
                | Node::Ult {
                    nid, left, right, ..
                }
                | Node::Eq {
                    nid, left, right, ..
                }
                | Node::And {
                    nid, left, right, ..
                }
                | Node::Or {
                    nid, left, right, ..
                }
                | Node::Divu {
                    nid, left, right, ..
                } => {
                    let child1 = noderef_to_nid(left);
                    let child2 = noderef_to_nid(right);
                    node_to_children
                        .entry(*nid)
                        .or_insert_with(Vec::new)
                        .append(&mut vec![child1, child2]);
                    node_lookup.insert(*nid, node);
                }
                Node::Ite {
                    nid,
                    cond,
                    left,
                    right,
                    ..
                }
                | Node::Write {
                    nid,
                    memory: cond,
                    address: left,
                    value: right,
                    ..
                } => {
                    let child1 = noderef_to_nid(cond);
                    let child2 = noderef_to_nid(left);
                    let child3 = noderef_to_nid(right);
                    node_to_children
                        .entry(*nid)
                        .or_insert_with(Vec::new)
                        .append(&mut vec![child1, child2, child3]);
                    node_lookup.insert(*nid, node);
                }
                Node::Input { nid, .. } => {
                    node_to_children.entry(*nid).or_insert_with(Vec::new);
                    node_lookup.insert(*nid, node);
                }
                Node::State {
                    nid, init, name, ..
                } => {
                    if init.is_none() {
                        node_to_children.entry(*nid).or_insert_with(Vec::new);
                    } else {
                        let child = noderef_to_nid(init.as_ref().unwrap());
                        node_to_children
                            .entry(*nid)
                            .or_insert_with(Vec::new)
                            .append(&mut vec![child]);
                        states.push(*nid);
                    }

                    Self::map_to_reg_spot(&mut registers, *nid, name.as_ref().unwrap().as_str());

                    node_lookup.insert(*nid, node);
                }
                Node::Next {
                    nid, state, next, ..
                } => {
                    let child1 = noderef_to_nid(state);
                    let child2 = noderef_to_nid(next);
                    node_to_children
                        .entry(*nid)
                        .or_insert_with(Vec::new)
                        .append(&mut vec![child1, child2]);
                    roots.push(*nid);
                    node_lookup.insert(*nid, node);
                }
                Node::Bad { nid, cond, .. } => {
                    let child = noderef_to_nid(cond);
                    node_to_children
                        .entry(*nid)
                        .or_insert_with(Vec::new)
                        .append(&mut vec![child]);
                    roots.push(*nid);
                    node_lookup.insert(*nid, node);
                }
                Node::Comment(_) => unreachable!(),
            };
        }

        let mut graph = Self {
            roots,
            registers,
            states,
            node_lookup,
            node_to_children,
            ..Default::default()
        };

        graph.initialize_states();
        graph.sugiyama();
        graph
    }

    fn initialize_states(&mut self) {
        let states = self.states.clone();
        self.tick = -1;

        for state in states {
            let node_ref = {
                let si = self.node_lookup.get(&state).unwrap();
                si.origin.clone()
            };

            if let Node::State { init, .. } = &*node_ref.borrow() {
                let init = noderef_to_nid(init.as_ref().unwrap());
                let value = self.evaluate(&init);
                let si = self.node_lookup.get_mut(&state).unwrap();
                si.set_value(value);
            } else {
                panic!("Can't initialize non state node")
            };
        }
        self.tick = 0;
    }

    fn map_to_reg_spot(arr: &mut [Option<Nid>; 32], spot: Nid, str: &str) {
        let index = match str {
            "zero" => Register::Zero,
            "ra" => Register::Ra,
            "sp" => Register::Sp,
            "gp" => Register::Gp,
            "tp" => Register::Tp,
            "t0" => Register::T0,
            "t1" => Register::T1,
            "t2" => Register::T2,
            "s0" => Register::Fp,
            "s1" => Register::S1,
            "a0" => Register::A0,
            "a1" => Register::A1,
            "a2" => Register::A2,
            "a3" => Register::A3,
            "a4" => Register::A4,
            "a5" => Register::A5,
            "a6" => Register::A6,
            "a7" => Register::A7,
            "s2" => Register::S2,
            "s3" => Register::S3,
            "s4" => Register::S4,
            "s5" => Register::S5,
            "s6" => Register::S6,
            "s7" => Register::S7,
            "s8" => Register::S8,
            "s9" => Register::S9,
            "s10" => Register::S10,
            "s11" => Register::S11,
            "t3" => Register::T3,
            "t4" => Register::T4,
            "t5" => Register::T5,
            "t6" => Register::T6,
            _ => return,
        };

        arr[index as usize] = Some(spot);
    }

    pub(crate) fn interact(&mut self, ui: &mut Ui) {
        if ui.rect_contains_pointer(ui.min_rect()) && ui.ctx().input(|i| i.pointer.primary_down()) {
            ui.ctx().input(|i| self.pan += i.pointer.delta());
        }
        if ui.rect_contains_pointer(ui.min_rect()) {
            ui.ctx().input(|i| self.pan += i.scroll_delta);
        }
    }

    pub(crate) fn tick_over(&mut self) -> isize {
        self.tick += 1;

        let roots = self.roots.clone();
        let results: Vec<_> = roots.iter().map(|x| self.evaluate(x)).collect();

        roots.iter().zip(results).for_each(|(spot, value)| {
            let (node_ref, val_cur) = {
                let s = self.nid_to_spot(spot);
                (s.origin.clone(), s.current_value.clone())
            };

            match &*node_ref.borrow() {
                Node::Next { state, .. } => {
                    let state = noderef_to_nid(state);
                    let state = self.node_lookup.get_mut(&state).unwrap();
                    state.set_value(value);
                }
                Node::Bad { name, .. } => {
                    if val_cur == Boolean(true) {
                        debug!("Bad is true: {}", name.as_ref().unwrap());
                        self.in_bad_state = true;
                    }
                }
                _ => unreachable!("Only Bad and Next nodes can be roots"),
            };
        });

        self.tick
    }

    pub(crate) fn nid_to_spot(&self, nid: &Nid) -> &Spot {
        self.node_lookup.get(nid).unwrap()
    }

    pub(crate) fn evaluate(&mut self, nid: &Nid) -> Value {
        let mut spot = self.node_lookup.get_mut(nid).unwrap();
        spot.old_value = spot.current_value.clone();

        if self.tick == spot.tick {
            return spot.current_value.clone();
        }

        spot.tick = self.tick;

        let (node_ref, current_value) = {
            let spot = self.nid_to_spot(nid);
            (spot.origin.clone(), spot.current_value.clone())
        };

        let new_value = match &*node_ref.borrow() {
            Node::Const { .. } => current_value,
            Node::Read {
                memory, address, ..
            } => {
                let memory = &noderef_to_nid(memory);
                let memory = self.evaluate(memory);
                let address = &noderef_to_nid(address);
                match (&memory, &self.evaluate(address)) {
                    (Array(m), Bitvector(i)) => Bitvector(*m.get(i).unwrap()),
                    _ => unreachable!(),
                }
            }
            Node::Write {
                nid,
                memory,
                address,
                value,
                ..
            } => {
                let memory = &noderef_to_nid(memory);
                let address = &noderef_to_nid(address);
                let value = &noderef_to_nid(value);

                match (
                    self.evaluate(memory),
                    self.evaluate(address),
                    self.evaluate(value),
                ) {
                    (Array(mut m), Bitvector(i), Bitvector(x)) => {
                        m.insert(i, x);
                        Array(m)
                    }
                    x => unreachable!("caused by {} {:?}", nid, x),
                }
            }
            Node::Add { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) + self.evaluate(spot2)
            }
            Node::Sub { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) - self.evaluate(spot2)
            }
            Node::Mul { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) * self.evaluate(spot2)
            }
            Node::Div { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) / self.evaluate(spot2)
            }
            Node::Rem { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) % self.evaluate(spot2)
            }
            Node::Sll { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) << self.evaluate(spot2)
            }
            Node::Srl { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) >> self.evaluate(spot2)
            }
            Node::Ult { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                Boolean(self.evaluate(spot1) < self.evaluate(spot2))
            }
            Node::Divu { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1).divu(self.evaluate(spot2))
            }
            Node::Ext { value, .. } => {
                let spot = &noderef_to_nid(value);
                let result = self.evaluate(spot);
                if let Boolean(b) = result {
                    Bitvector(Concrete(u64::from(b)))
                } else {
                    result
                }
            }
            Node::Ite {
                cond, left, right, ..
            } => {
                let cond = &noderef_to_nid(cond);
                match &self.evaluate(cond) {
                    Boolean(b) => {
                        if *b {
                            let left = &noderef_to_nid(left);
                            self.evaluate(left)
                        } else {
                            let right = &noderef_to_nid(right);
                            self.evaluate(right)
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Node::Eq { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                Boolean(self.evaluate(spot1) == self.evaluate(spot2))
            }
            Node::And { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) & self.evaluate(spot2)
            }
            Node::Or { left, right, .. } => {
                let spot1 = &noderef_to_nid(left);
                let spot2 = &noderef_to_nid(right);
                self.evaluate(spot1) | self.evaluate(spot2)
            }
            Node::Not { value, .. } => {
                let spot = &noderef_to_nid(value);
                !self.evaluate(spot)
            }
            Node::State { init, sort, .. } => {
                if init.is_some() {
                    current_value
                } else if let NodeType::Memory { .. } = sort {
                    current_value
                } else {
                    let result = if self.is_ascii {
                        if !self.input_ascii.is_empty() {
                            self.input_ascii.remove(0) as u64
                        } else {
                            0
                        }
                    } else {
                        let val = self.input_number as u64;
                        self.input_number = 0;
                        val
                    };
                    self.consumed_inputs.push(format!("{result}"));
                    Bitvector(Concrete(result))
                }
            }
            Node::Next { next, .. } => {
                let spot = &noderef_to_nid(next);
                self.evaluate(spot)
            }
            Node::Input { sort, .. } => {
                let result = if self.is_ascii {
                    let chars_taken = match sort {
                        NodeType::Bit => unreachable!(),
                        NodeType::Word => 8,
                        NodeType::Memory => unreachable!(),
                        NodeType::Input1Byte => 1,
                        NodeType::Input2Byte => 2,
                        NodeType::Input3Byte => 3,
                        NodeType::Input4Byte => 4,
                        NodeType::Input5Byte => 5,
                        NodeType::Input6Byte => 6,
                        NodeType::Input7Byte => 7,
                    };

                    let mut nr: u64 = 0;
                    for i in 0..chars_taken {
                        let char = if !self.input_ascii.is_empty() {
                            self.input_ascii.remove(0) as u64
                        } else {
                            0
                        };
                        nr |= char << (i * 8);
                    }
                    nr
                } else {
                    let val = self.input_number as u64;
                    self.input_number = 0;
                    val
                };
                self.consumed_inputs.push(format!("{result}"));
                Bitvector(Concrete(result))
            }
            Node::Bad { cond, .. } => {
                let spot = &noderef_to_nid(cond);
                self.evaluate(spot)
            }
            Node::Comment(_) => unreachable!(),
        };

        let mut spot = self.node_lookup.get_mut(nid).unwrap();
        spot.current_value = new_value.clone();
        new_value
    }

    pub(crate) fn system_state(
        &self,
    ) -> (
        Vec<Value>,
        Option<u64>,
        bool,
        IndexMap<MachineWord, MachineWord>,
    ) {
        let regs = self
            .registers
            .as_ref()
            .iter()
            .map(|x| {
                if let Some(x) = x {
                    let s = self.nid_to_spot(x);
                    s.current_value.clone()
                } else {
                    Bitvector(Concrete(0))
                }
            })
            .collect::<Vec<Value>>();

        let mut pc = None;
        let mut vm = IndexMap::new();
        let mut kernel_mode = false;

        for x in &self.states {
            let s = self.nid_to_spot(x);
            match &*s.origin.borrow() {
                Node::State { name, .. } => {
                    let name = name.as_ref().unwrap().as_str();
                    if name == "virtual-memory" {
                        if let Array(hm) = &s.current_value {
                            vm = hm.clone();
                        }
                    }

                    if name.starts_with("pc=") && s.current_value == Boolean(true) {
                        if pc.is_some() {
                            panic!("Multiple PCs active at once: {:?} and {:?}", pc, x);
                        }
                        pc = Some(u64::from_str_radix(&name[5..], 16).unwrap());
                    }

                    if name.starts_with("kernel") {
                        kernel_mode |= Boolean(true) == s.current_value;
                    }
                }
                _ => unreachable!(),
            };
        }

        (regs, pc, kernel_mode, vm)
    }

    pub(crate) fn a7_is_read_or_exit(&self) -> bool {
        self.nid_to_spot(&self.registers[17].unwrap()).current_value == Bitvector(Concrete(63))
            || self.nid_to_spot(&self.registers[17].unwrap()).current_value
                == Bitvector(Concrete(93))
    }

    pub(crate) fn is_in_kernel_mode(&self) -> bool {
        self.states
            .iter()
            .map(|x| self.nid_to_spot(x))
            .filter(|x| match &*x.origin.borrow() {
                Node::State { name, .. } => name.as_ref().unwrap().starts_with("kernel"),
                _ => unreachable!(),
            })
            .map(|x| x.current_value == Boolean(true))
            .reduce(|a, x| a || x)
            .unwrap()
    }
}

pub(crate) fn noderef_to_nid(n: &NodeRef) -> Nid {
    match &*n.borrow() {
        Node::Const { nid, .. }
        | Node::Read { nid, .. }
        | Node::Write { nid, .. }
        | Node::Add { nid, .. }
        | Node::Sub { nid, .. }
        | Node::Mul { nid, .. }
        | Node::Div { nid, .. }
        | Node::Rem { nid, .. }
        | Node::Sll { nid, .. }
        | Node::Srl { nid, .. }
        | Node::Ult { nid, .. }
        | Node::Ext { nid, .. }
        | Node::Ite { nid, .. }
        | Node::Eq { nid, .. }
        | Node::And { nid, .. }
        | Node::Not { nid, .. }
        | Node::State { nid, .. }
        | Node::Next { nid, .. }
        | Node::Input { nid, .. }
        | Node::Divu { nid, .. }
        | Node::Or { nid, .. }
        | Node::Bad { nid, .. } => *nid,
        Node::Comment(_) => unreachable!(),
    }
}

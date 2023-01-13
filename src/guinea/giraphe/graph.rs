use std::collections::HashMap;
use std::default::Default;
use std::iter::zip;

use egui::{Ui, Vec2};
use log::trace;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Array, Bitvector, Boolean};
use crate::guinea::giraphe::{Giraphe, MachineWord, Spot, Value};
use crate::unicorn::{Model, Nid, Node, NodeRef, NodeType};

// TODO:
//   inputs in the graph
//   preprocess the graph
//    - collapse if then else block
//    - collapse input gathering
//    - unroll once to remove all unnecessary extras
//   better layout:
//    - directly dependant nodes near each other
//    - less density
impl Giraphe {
    pub fn from(model: &Model) -> Self {
        assert!(
            !model.lines.is_empty(),
            "Can't convert model before it was renumbered!"
        );

        let mut spot_lookup: HashMap<Nid, Spot> = HashMap::new();
        let mut leaves: Vec<Nid> = Vec::new();
        let mut inputs: Vec<Nid> = Vec::new();

        let mut states: Vec<Nid> = Vec::new();
        let mut registers: [Option<Nid>; 32] = Default::default();

        for node in &model.lines {
            let n = &*node.borrow();
            let spot = match n {
                Node::Comment(c) => {
                    trace!("Skipping comment in model2graph conversion: {c}");
                    continue;
                }
                _ => Spot::from(node),
            };

            match &*node.borrow() {
                Node::Const { nid, .. }
                | Node::Not { nid, .. }
                | Node::Ext { nid, .. }
                | Node::Read { nid, .. }
                | Node::Add { nid, .. }
                | Node::Sub { nid, .. }
                | Node::Mul { nid, .. }
                | Node::Div { nid, .. }
                | Node::Rem { nid, .. }
                | Node::Sll { nid, .. }
                | Node::Srl { nid, .. }
                | Node::Ult { nid, .. }
                | Node::Eq { nid, .. }
                | Node::And { nid, .. }
                | Node::Ite { nid, .. }
                | Node::Write { nid, .. } => {
                    spot_lookup.insert(*nid, spot);
                }
                Node::Input { nid, .. } => {
                    inputs.push(*nid);
                    spot_lookup.insert(*nid, spot);
                }
                Node::State {
                    nid, init, name, ..
                } => {
                    if init.is_none() {
                        inputs.push(*nid);
                    } else {
                        states.push(*nid);
                    }

                    Self::map_to_reg_spot(&mut registers, *nid, name.as_ref().unwrap().as_str());

                    spot_lookup.insert(*nid, spot);
                }
                Node::Next { nid, .. } | Node::Bad { nid, .. } => {
                    leaves.push(*nid);
                    spot_lookup.insert(*nid, spot);
                }
                Node::Comment(_) => unreachable!(),
            };
        }

        states.sort_by(|x, y| {
            let x = spot_lookup.get(x).unwrap();
            let y = spot_lookup.get(y).unwrap();
            let r = match (&*x.origin.borrow(), &*y.origin.borrow()) {
                (Node::State { name: t1, .. }, Node::State { name: t2, .. }) => t1.cmp(t2),
                _ => unreachable!(),
            };
            r
        });

        let mut g = Self {
            tick: 0,
            spot_lookup,
            roots: leaves,
            inputs,
            registers,
            is_ascii: false,
            input_ascii: String::default(),
            input_number: 0,
            states: states.clone(),
            pan: Vec2::default(),
            input_queue: vec![],
            layout: Default::default(),
        };

        g.tick = -1;
        for si in states {
            let node_ref = {
                let si = g.spot_lookup.get(&si).unwrap();
                si.origin.clone()
            };

            if let Node::State { init, .. } = &*node_ref.borrow() {
                let init = noderef_to_nid(init.as_ref().unwrap());
                let value = g.evaluate(&init);
                let si = g.spot_lookup.get_mut(&si).unwrap();
                si.set_value(value);
            } else {
                panic!("Can't initialize non state node")
            };
        }
        g.tick = 0;
        g.sugiyamer();
        g
    }

    fn map_to_reg_spot(arr: &mut [Option<Nid>; 32], spot: Nid, str: &str) {
        match str {
            "zero" => arr[0] = Some(spot),
            "ra" => arr[1] = Some(spot),
            "sp" => arr[2] = Some(spot),
            "gp" => arr[3] = Some(spot),
            "tp" => arr[4] = Some(spot),
            "t0" => arr[5] = Some(spot),
            "t1" => arr[6] = Some(spot),
            "t2" => arr[7] = Some(spot),
            "s0" => arr[8] = Some(spot),
            "s1" => arr[9] = Some(spot),
            "a0" => arr[10] = Some(spot),
            "a1" => arr[11] = Some(spot),
            "a2" => arr[12] = Some(spot),
            "a3" => arr[13] = Some(spot),
            "a4" => arr[14] = Some(spot),
            "a5" => arr[15] = Some(spot),
            "a6" => arr[16] = Some(spot),
            "a7" => arr[17] = Some(spot),
            "s2" => arr[18] = Some(spot),
            "s3" => arr[19] = Some(spot),
            "s4" => arr[20] = Some(spot),
            "s5" => arr[21] = Some(spot),
            "s6" => arr[22] = Some(spot),
            "s7" => arr[23] = Some(spot),
            "s8" => arr[24] = Some(spot),
            "s9" => arr[25] = Some(spot),
            "s10" => arr[26] = Some(spot),
            "s11" => arr[27] = Some(spot),
            "t3" => arr[28] = Some(spot),
            "t4" => arr[29] = Some(spot),
            "t5" => arr[30] = Some(spot),
            "t6" => arr[31] = Some(spot),
            _ => {}
        }
    }

    pub fn interact(&mut self, ui: &mut Ui) {
        if ui.rect_contains_pointer(ui.min_rect()) && ui.ctx().input().pointer.primary_down() {
            self.pan += ui.ctx().input().pointer.delta();
        }
    }

    pub fn tick_over(&mut self) -> isize {
        self.tick += 1;

        let leaves = self.roots.clone();
        let mut res = Vec::new();
        for leaf in leaves {
            let value = self.evaluate(&leaf);
            res.push(value);
        }

        for (sp, val) in zip(&self.roots, res) {
            let (node_ref, val_cur) = {
                let s = self.nid_to_spot(sp);
                (s.origin.clone(), s.val_cur.clone())
            };

            match &*node_ref.borrow() {
                Node::Next { state, .. } => {
                    let state = noderef_to_nid(state);
                    let state = self.spot_lookup.get_mut(&state).unwrap();
                    state.set_value(val);
                }
                Node::Bad { name, .. } => {
                    if val_cur == Boolean(true) {
                        println!("Bad is true: {}", name.as_ref().unwrap());
                    }
                }
                _ => unreachable!("Only Bad and Next nodes can be leaves"),
            };
        }

        self.tick
    }

    pub fn nid_to_spot(&self, nid: &Nid) -> &Spot {
        self.spot_lookup.get(nid).unwrap()
    }

    pub fn evaluate(&mut self, nid: &Nid) -> Value {
        {
            let mut spot = self.spot_lookup.get_mut(nid).unwrap();
            spot.val_old = spot.val_cur.clone();

            if self.tick == spot.tick {
                return spot.val_cur.clone();
            }
            spot.tick = if self.tick > 0 { self.tick } else { 0 };
        }

        let (node_ref, val_cur) = {
            let spot = self.nid_to_spot(nid);
            (spot.origin.clone(), spot.val_cur.clone())
        };

        let val = {
            let x = match &*node_ref.borrow() {
                Node::Const { .. } => val_cur,
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
                Node::Ext { value, .. } => {
                    let spot = &noderef_to_nid(value);
                    let v = self.evaluate(spot);
                    if let Boolean(b) = v {
                        Bitvector(Concrete(u64::from(b)))
                    } else {
                        v
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
                Node::Not { value, .. } => {
                    let spot = &noderef_to_nid(value);
                    !self.evaluate(spot)
                }
                Node::State { .. } => val_cur,
                Node::Next { next, .. } => {
                    let spot = &noderef_to_nid(next);
                    self.evaluate(spot)
                }
                Node::Input { sort, .. } => {
                    let ret = if self.is_ascii {
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
                    self.input_queue.push(format!("{ret}"));
                    Bitvector(Concrete(ret))
                }
                Node::Bad { cond, .. } => {
                    let spot = &noderef_to_nid(cond);
                    self.evaluate(spot)
                }
                Node::Comment(_) => unreachable!(),
            };
            x
        };

        let mut spot = self.spot_lookup.get_mut(nid).unwrap();

        spot.val_cur = val.clone();

        val
    }

    pub fn system_state(&self) -> (Vec<Value>, u64, bool, HashMap<MachineWord, MachineWord>) {
        let regs = self
            .registers
            .as_ref()
            .iter()
            .map(|x| {
                if let Some(x) = x {
                    let s = self.nid_to_spot(x);
                    s.val_cur.clone()
                } else {
                    Bitvector(Concrete(0))
                }
            })
            .collect::<Vec<Value>>();

        let mut pc = 0;
        let mut vm = HashMap::new();
        let mut kernel_mode = false;

        for x in &self.states {
            let s = self.nid_to_spot(x);
            match &*s.origin.borrow() {
                Node::State { name, .. } => {
                    let name = name.as_ref().unwrap().as_str();
                    if name == "virtual-memory" {
                        if let Array(hm) = &s.val_cur {
                            vm = hm.clone();
                        }
                    }

                    if name.starts_with("pc=") && s.val_cur == Boolean(true) {
                        if pc != 0 {
                            panic!("Multiple PCs active at once: {:?} and {:?}", pc, x);
                        }
                        pc = u64::from_str_radix(&name[5..], 16).unwrap();
                    }

                    if name.starts_with("kernel") {
                        kernel_mode |= Boolean(true) == s.val_cur;
                    }
                }
                _ => unreachable!(),
            };
        }

        (regs, pc, kernel_mode, vm)
    }

    pub fn a7_is_read_or_exit(&self) -> bool {
        self.nid_to_spot(&self.registers[17].unwrap()).val_cur == Bitvector(Concrete(63))
            || self.nid_to_spot(&self.registers[17].unwrap()).val_cur == Bitvector(Concrete(93))
    }

    pub fn is_in_kernel_mode(&self) -> bool {
        self.states
            .iter()
            .map(|x| self.nid_to_spot(x))
            .filter(|x| match &*x.origin.borrow() {
                Node::State { name, .. } => name.as_ref().unwrap().starts_with("kernel"),
                _ => unreachable!(),
            })
            .map(|x| x.val_cur == Boolean(true))
            .reduce(|a, x| a || x)
            .unwrap()
    }

    pub fn spot_parents(&self, nid: Nid) -> Vec<Nid> {
        match &*self.nid_to_spot(&nid).origin.borrow() {
            Node::Const { .. } | Node::Input { .. } => vec![],
            Node::Bad { cond: a, .. } | Node::Ext { value: a, .. } | Node::Not { value: a, .. } => {
                vec![noderef_to_nid(a)]
            }
            Node::Read {
                memory: a,
                address: b,
                ..
            }
            | Node::Add {
                left: a, right: b, ..
            }
            | Node::Sub {
                left: a, right: b, ..
            }
            | Node::Mul {
                left: a, right: b, ..
            }
            | Node::Div {
                left: a, right: b, ..
            }
            | Node::Rem {
                left: a, right: b, ..
            }
            | Node::Sll {
                left: a, right: b, ..
            }
            | Node::Srl {
                left: a, right: b, ..
            }
            | Node::Ult {
                left: a, right: b, ..
            }
            | Node::Eq {
                left: a, right: b, ..
            }
            | Node::And {
                left: a, right: b, ..
            }
            | Node::Next {
                state: a, next: b, ..
            } => vec![noderef_to_nid(a), noderef_to_nid(b)],
            Node::Write {
                memory: a,
                address: b,
                value: c,
                ..
            }
            | Node::Ite {
                cond: a,
                left: b,
                right: c,
                ..
            } => vec![noderef_to_nid(a), noderef_to_nid(b), noderef_to_nid(c)],
            Node::State { init, .. } => {
                if let Some(a) = init {
                    vec![noderef_to_nid(a)]
                } else {
                    vec![]
                }
            }
            Node::Comment(_) => unreachable!(),
        }
    }
}

pub fn noderef_to_nid(n: &NodeRef) -> Nid {
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
        | Node::Bad { nid, .. } => *nid,
        Node::Comment(_) => unreachable!(),
    }
}

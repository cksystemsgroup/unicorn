use crate::guinea::giraphe::graph::map_node_ref_to_nid;
use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Array, Bitvector, Boolean, Immediate};
use crate::guinea::giraphe::{Giraphe, Spot, SpotRef, Value};
use crate::unicorn::{Node, NodeRef, NodeType};
use egui::{Response, Ui, Widget};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

impl Spot {
    pub fn from(n: &NodeRef) -> SpotRef {
        let val_cur = match &*n.borrow() {
            Node::Input { .. } => Bitvector(Concrete(1)),
            Node::Const { sort, imm, .. } => match sort {
                NodeType::Bit => Boolean(*imm != 0),
                NodeType::Word => Bitvector(Concrete(*imm)),
                _ => unreachable!(),
            },
            Node::State {
                sort, init: None, ..
            } => match sort {
                NodeType::Word
                | NodeType::Input1Byte
                | NodeType::Input2Byte
                | NodeType::Input3Byte
                | NodeType::Input4Byte
                | NodeType::Input5Byte
                | NodeType::Input6Byte
                | NodeType::Input7Byte => Bitvector(Concrete(0)), // TODO: give proper input
                NodeType::Memory => Value::default_array(),
                x => unreachable!("caused by {:?}", x),
            },
            _ => Value::Undefined,
        };

        Rc::new(RefCell::new(Self {
            tick: 0,
            val_old: Value::Undefined,
            val_cur,
            origin: n.clone(),
            position: Default::default(),
        }))
    }

    pub fn set_position(&mut self, x: f32, y: f32) {
        self.position.x = x;
        self.position.y = y;
    }

    pub fn evaluate(&mut self, graph: &Giraphe) -> Value {
        if self.tick == graph.tick {
            return self.val_cur.clone();
        }
        self.tick = if graph.tick > 0 { graph.tick } else { 0 };
        self.val_old = self.val_cur.clone();

        let node_to_spot = |x| {
            let nid = map_node_ref_to_nid(x);
            graph.spot_lookup.get(&nid).unwrap()
        };

        let val = match &*self.origin.borrow() {
            Node::Const { .. } => self.val_cur.clone(),
            Node::Read {
                memory, address, ..
            } => {
                let memory = &mut *node_to_spot(memory).borrow_mut();
                memory.evaluate(graph);
                let address = &mut *node_to_spot(address).borrow_mut();
                address.evaluate(graph);
                match (&memory.val_cur, &address.val_cur) {
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
                let memory = &mut *node_to_spot(memory).borrow_mut();
                memory.evaluate(graph);
                let address = &mut *node_to_spot(address).borrow_mut();
                address.evaluate(graph);
                let value = &mut *node_to_spot(value).borrow_mut();
                value.evaluate(graph);

                match (memory.val_cur.clone(), &address.val_cur, &value.val_cur) {
                    (Array(mut m), Bitvector(i), Bitvector(x)) => {
                        m.insert(*i, *x);
                        Array(m)
                    }
                    x => unreachable!("caused by {} {:?}", nid, x),
                }
            }
            Node::Add { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                v1 + spot2.evaluate(graph)
            }
            Node::Sub { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                v1 - spot2.evaluate(graph)
            }
            Node::Mul { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                v1 * spot2.evaluate(graph)
            }
            Node::Div { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                v1 / spot2.evaluate(graph)
            }
            Node::Rem { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                v1 % spot2.evaluate(graph)
            }
            Node::Sll { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                v1 << spot2.evaluate(graph)
            }
            Node::Srl { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                v1 >> spot2.evaluate(graph)
            }
            Node::Ult { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                let v2 = spot2.evaluate(graph);

                Boolean(v1 < v2)
            }
            Node::Ext { value, .. } => {
                let spot = &mut *node_to_spot(value).borrow_mut();
                spot.evaluate(graph)
            }
            Node::Ite {
                cond, left, right, ..
            } => {
                let cond = &mut *node_to_spot(cond).borrow_mut();
                match &cond.evaluate(graph) {
                    Boolean(b) => {
                        if *b {
                            let left = &mut *node_to_spot(left).borrow_mut();
                            left.evaluate(graph)
                        } else {
                            let right = &mut *node_to_spot(right).borrow_mut();
                            right.evaluate(graph)
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Node::Eq { left, right, .. } => {
                let same = std::ptr::eq(node_to_spot(left), node_to_spot(right));
                if !same {
                    let v1 = {
                        let spot1 = &mut *node_to_spot(left).borrow_mut();
                        spot1.evaluate(graph)
                    };
                    let spot2 = &mut *node_to_spot(right).borrow_mut();
                    Boolean(v1 == spot2.evaluate(graph))
                } else {
                    Boolean(true)
                }
            }
            Node::And { left, right, .. } => {
                let v1 = {
                    let spot1 = &mut *node_to_spot(left).borrow_mut();
                    spot1.evaluate(graph)
                };
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                let v2 = spot2.evaluate(graph);
                v1 & v2
            }
            Node::Not { value, .. } => {
                let spot = &mut *node_to_spot(value).borrow_mut();
                !spot.evaluate(graph)
            }
            Node::State { .. } => self.val_cur.clone(),
            Node::Next { next, .. } => {
                let spot1 = &mut *node_to_spot(next).borrow_mut();
                spot1.evaluate(graph)
            }
            Node::Input { .. } => self.val_cur.clone(),
            Node::Bad { cond, .. } => {
                let spot = &mut *node_to_spot(cond).borrow_mut();
                spot.evaluate(graph)
            }
            Node::Comment(_) => unreachable!(),
        };

        self.val_cur = val.clone();

        val
    }

    pub(crate) fn title(&self) -> &str {
        match &*self.origin.borrow() {
            Node::Const { .. } => "Constant",
            Node::Read { .. } => "Read",
            Node::Write { .. } => "Write",
            Node::Add { .. } => "Add",
            Node::Sub { .. } => "Sub",
            Node::Mul { .. } => "Mul",
            Node::Div { .. } => "Division",
            Node::Rem { .. } => "Remainder",
            Node::Sll { .. } => "Shift Left",
            Node::Srl { .. } => "Shift Right",
            Node::Ult { .. } => "Less Than",
            Node::Ext { .. } => "Extend",
            Node::Ite { .. } => "If-then-else",
            Node::Eq { .. } => "Equality",
            Node::And { .. } => "And",
            Node::Not { .. } => "Not",
            Node::State { .. } => "State",
            Node::Next { .. } => "Next",
            Node::Input { .. } => "Input",
            Node::Bad { .. } => "Bad",
            Node::Comment(_) => unreachable!(),
        }
    }
}

impl Widget for Spot {
    fn ui(self, ui: &mut Ui) -> Response {
        let name = match &*self.origin.borrow() {
            Node::State { name, .. } => name.clone().unwrap(),
            Node::Bad { name, .. } => name.clone().unwrap(),
            _ => "no name".to_string(),
        };
        ui.vertical(|ui| {
            ui.heading(self.title());
            ui.separator();
            ui.label(name);
            let was = format!("Was: {}", self.val_old);
            let now = format!("Is: {}", self.val_cur);
            ui.label(format!("Tick: {}", self.tick));
            ui.label(was);
            ui.label(now);
        })
        .response
    }
}

impl Value {
    pub fn _default_bool() -> Self {
        Boolean(false)
    }

    pub fn default_array() -> Self {
        Self::Array(HashMap::new())
    }

    pub fn _default_string() -> Self {
        Self::String("no name".to_string())
    }

    pub fn _default_imm() -> Self {
        Immediate(0)
    }
}

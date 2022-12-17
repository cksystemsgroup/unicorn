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
            Node::Input { .. } => Bitvector(Concrete(0)),
            Node::Const { sort, imm, .. } => match sort {
                NodeType::Bit => Boolean(*imm != 0),
                NodeType::Word => Bitvector(Concrete(*imm)),
                _ => unreachable!(),
            },
            Node::State { init: None, .. } => Bitvector(Concrete(0)),
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

    pub fn _is_different(&self) -> bool {
        self.val_cur != self.val_old
    }

    pub fn evaluate(&mut self, graph: &Giraphe) -> Value {
        if self.tick == graph.tick {
            return self.val_cur.clone();
        }
        self.tick = graph.tick;
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
                let memory = &*node_to_spot(memory).borrow();
                let address = &*node_to_spot(address).borrow();
                match (&memory.val_cur, &address.val_cur) {
                    (Array(m), Bitvector(i)) => Bitvector(*m.get(i).unwrap()),
                    _ => unreachable!(),
                }
            }
            Node::Write {
                memory,
                address,
                value,
                ..
            } => {
                let memory = &*node_to_spot(memory).borrow();
                let address = &*node_to_spot(address).borrow();
                let value = &*node_to_spot(value).borrow();
                match (memory.val_cur.clone(), &address.val_cur, &value.val_cur) {
                    (Array(mut m), Bitvector(i), Bitvector(x)) => {
                        m.insert(*i, *x);
                        Array(m.clone())
                    }
                    _ => unreachable!(),
                }
            }
            Node::Add { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) + spot2.evaluate(graph)
            }
            Node::Sub { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) - spot2.evaluate(graph)
            }
            Node::Mul { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) * spot2.evaluate(graph)
            }
            Node::Div { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) / spot2.evaluate(graph)
            }
            Node::Rem { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) % spot2.evaluate(graph)
            }
            Node::Sll { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) << spot2.evaluate(graph)
            }
            Node::Srl { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) >> spot2.evaluate(graph)
            }
            Node::Ult { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                Boolean(spot1.evaluate(graph) < spot2.evaluate(graph))
            }
            Node::Ext { value, .. } => {
                let spot = &mut *node_to_spot(value).borrow_mut();
                spot.evaluate(graph)
            }
            Node::Ite {
                cond, left, right, ..
            } => {
                let cond = &mut *node_to_spot(cond).borrow_mut();
                let left = &mut *node_to_spot(left).borrow_mut();
                let right = &mut *node_to_spot(right).borrow_mut();

                match (&cond.evaluate(graph), left, right) {
                    (Boolean(b), l, r) => {
                        if *b {
                            l.evaluate(graph)
                        } else {
                            r.evaluate(graph)
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Node::Eq { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                Boolean(spot1.evaluate(graph) == spot2.evaluate(graph))
            }
            Node::And { left, right, .. } => {
                let spot1 = &mut *node_to_spot(left).borrow_mut();
                let spot2 = &mut *node_to_spot(right).borrow_mut();
                spot1.evaluate(graph) & spot2.evaluate(graph)
            }
            Node::Not { value, .. } => {
                let spot = &mut *node_to_spot(value).borrow_mut();
                !spot.evaluate(graph)
            }
            Node::State { init, .. } => match self.val_old {
                Value::Undefined => {
                    let spot = &mut *node_to_spot(init.as_ref().unwrap()).borrow_mut();
                    self.val_old = spot.evaluate(graph);
                    self.val_old.clone()
                }
                _ => self.val_old.clone(),
            }, // <- here
            Node::Next { state, next, .. } => {
                let spot1 = &mut *node_to_spot(next).borrow_mut();
                let spot2 = &mut *node_to_spot(state).borrow_mut();
                let next = spot1.evaluate(graph);
                spot2.val_cur = next.clone();
                next
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

    fn title(&self) -> &str {
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
        ui.vertical(|ui| {
            ui.heading(self.title());
            ui.separator();
            let was = format!("Was: {}", self.val_old);
            let now = format!("Is: {}", self.val_cur);
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

    pub fn _default_array() -> Self {
        Self::Array(HashMap::new())
    }

    pub fn _default_string() -> Self {
        Self::String("no name".to_string())
    }

    pub fn _default_imm() -> Self {
        Immediate(0)
    }
}

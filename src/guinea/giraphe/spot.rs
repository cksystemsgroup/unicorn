use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Boolean, Immediate};
use crate::guinea::giraphe::{MachineWord, Spot, SpotRef, Value};
use crate::unicorn::{Node, NodeRef};
use egui::{Response, Ui, Widget};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

impl Spot {
    pub fn from(n: &NodeRef) -> SpotRef {
        let nid = &*n.borrow();
        let nid = match nid {
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
        };

        Rc::new(RefCell::new(Self {
            nid,
            tick: 0,
            val_old: Value::Undefined,
            val_cur: Value::Undefined,
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

    pub fn _evaluate(&mut self, _tick: usize) -> Value {
        // TODO: recursive evaluation
        Value::Undefined
    }
}

impl Widget for Spot {
    fn ui(self, ui: &mut Ui) -> Response {
        ui.vertical(|ui| {
            ui.heading("Dummy");
            ui.separator();
            ui.label("dummy");
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

impl PartialEq for Value {
    fn eq(&self, _other: &Self) -> bool {
        todo!()
    }
}

impl MachineWord {
    pub fn _from(nr: u64) -> Self {
        Concrete(nr)
    }
}

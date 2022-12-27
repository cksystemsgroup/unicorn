use std::collections::HashMap;

use egui::{Response, Ui, Widget};

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Bitvector, Boolean, Immediate};
use crate::guinea::giraphe::{Spot, Value};
use crate::unicorn::{Node, NodeRef, NodeType};

impl Spot {
    pub fn from(n: &NodeRef) -> Spot {
        let val_cur = match &*n.borrow() {
            Node::Input { .. } => Value::Undefined,
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
                | NodeType::Input7Byte => Value::Undefined,
                NodeType::Memory => Value::default_array(),
                x => unreachable!("caused by {:?}", x),
            },
            _ => Value::Undefined,
        };

        Self {
            tick: 0,
            val_old: Value::Undefined,
            val_cur,
            origin: n.clone(),
            position: Default::default(),
        }
    }

    pub fn from_spot(s: &Spot) -> Spot {
        Self {
            tick: s.tick,
            val_old: s.val_old.clone(),
            val_cur: s.val_cur.clone(),
            origin: s.origin.clone(),
            position: s.position,
        }
    }

    pub fn set_position(&mut self, x: f32, y: f32) {
        self.position.x = x;
        self.position.y = y;
    }

    pub fn set_value(&mut self, val: Value) {
        self.val_old = std::mem::replace(&mut self.val_cur, Value::Undefined);
        self.val_cur = val;
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

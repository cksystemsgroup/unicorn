use crate::guinea::giraphe::Value::{Boolean, Immediate};
use crate::guinea::giraphe::{Spot, SpotRef, Value};
use crate::unicorn::{Node, NodeRef};
use egui::{Response, Ui, Widget};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

impl Spot {
    pub fn from(n: &NodeRef) -> SpotRef {
        Rc::new(RefCell::new(Self {
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

    pub fn evaluate(&mut self, _tick: usize) -> Value {
        // TODO: recursive evaluation
        Value::Undefined
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

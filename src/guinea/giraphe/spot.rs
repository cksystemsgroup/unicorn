use egui::Color32;
use indexmap::IndexMap;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Bitvector, Boolean};
use crate::guinea::giraphe::{Spot, Value};
use crate::unicorn::{Node, NodeRef, NodeType};

impl Spot {
    pub(crate) fn from(n: &NodeRef) -> Spot {
        let current_value = match &*n.borrow() {
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
                NodeType::Memory => Value::Array(IndexMap::new()),
                x => unreachable!("caused by {:?}", x),
            },
            _ => Value::Undefined,
        };

        Self {
            tick: 0,
            old_value: Value::Undefined,
            current_value,
            origin: n.clone(),
        }
    }

    pub(crate) fn set_value(&mut self, val: Value) {
        self.old_value = std::mem::replace(&mut self.current_value, Value::Undefined);
        self.current_value = val;
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

    pub(crate) fn display_value_abbreviated(&self) -> String {
        match self.current_value {
            Boolean(x) => if x { "T" } else { "F" }.to_string(),
            Bitvector(x) => {
                let Concrete(x) = x;

                let value = format!("{}", x);
                if value.len() > 3 {
                    "...".to_string()
                } else {
                    value
                }
            }
            Value::Array(_) => "VM".to_string(),
            Value::Undefined => "?".to_string(),
        }
    }

    pub(crate) fn display_value(&self) -> String {
        match self.current_value {
            Boolean(x) => if x { "True" } else { "False" }.to_string(),
            Bitvector(x) => {
                let Concrete(x) = x;
                format!("{}", x)
            }
            Value::Array(_) => "Virtual Machine".to_string(),
            Value::Undefined => "Undefined".to_string(),
        }
    }

    pub(crate) fn node_name(&self) -> Option<String> {
        match &*self.origin.borrow() {
            Node::State { name, .. } => name.clone(),
            Node::Next { state, .. } => {
                if let Node::State { name, .. } = &*state.borrow() {
                    name.clone()
                } else {
                    unreachable!()
                }
            }
            Node::Input { name, .. } => Some(name.clone()),
            Node::Bad { name, .. } => name.clone(),
            _ => None,
        }
    }

    pub(crate) fn color(&self) -> Color32 {
        match &*self.origin.borrow() {
            Node::Const { .. } => Color32::from_rgb(188, 189, 59),
            Node::Read { .. } => Color32::from_rgb(156, 117, 95),
            Node::Write { .. } => Color32::from_rgb(237, 201, 72),
            Node::Add { .. }
            | Node::Sub { .. }
            | Node::Mul { .. }
            | Node::Div { .. }
            | Node::Rem { .. }
            | Node::Sll { .. }
            | Node::Ext { .. }
            | Node::Srl { .. } => Color32::from_rgb(255, 157, 167),
            Node::Ite { .. } => Color32::from_rgb(176, 122, 161),
            Node::Ult { .. } | Node::Eq { .. } | Node::And { .. } | Node::Not { .. } => {
                Color32::from_rgb(242, 142, 43)
            }
            Node::State { .. } => Color32::from_rgb(118, 183, 178),
            Node::Next { .. } => Color32::from_rgb(78, 121, 165),
            Node::Input { .. } => Color32::from_rgb(89, 161, 79),
            Node::Bad { .. } => Color32::from_rgb(225, 87, 89),
            Node::Comment(_) => unreachable!(),
        }
    }
}

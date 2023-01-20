mod draw;
mod graph;
mod operators;
mod spot;

use crate::guinea::giraphe::draw::Layout;
use crate::guinea::giraphe::MachineWord::Concrete;
use crate::unicorn::{Nid, NodeRef};
use egui::Vec2;
use indexmap::IndexMap;
use std::fmt::{Display, Formatter};

#[allow(unused)]
#[derive(Default, Debug)]
pub struct Giraphe {
    pub(crate) tick: isize,
    pub spot_lookup: IndexMap<Nid, Spot>,
    pub roots: Vec<Nid>,
    pub inputs: Vec<Nid>,
    pub states: Vec<Nid>,
    pub spot_to_children: IndexMap<Nid, Vec<Nid>>,
    pub spot_to_parents: IndexMap<Nid, Vec<Nid>>,
    pub pan: Vec2,
    pub registers: [Option<Nid>; 32],
    pub is_ascii: bool,
    pub input_ascii: String,
    pub input_number: u8,
    pub input_queue: Vec<String>,
    pub layout: Layout,
}

#[allow(unused)]
#[derive(Debug, Clone)]
pub struct Spot {
    tick: isize,
    pub(crate) val_old: Value,
    pub(crate) val_cur: Value,
    pub(crate) origin: NodeRef,
}

#[allow(unused)]
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum MachineWord {
    Concrete(u64),
    // Symbolic(?),
}

#[allow(unused)]
#[derive(Debug, Clone)]
pub enum Value {
    Boolean(bool),
    Bitvector(MachineWord),
    Array(IndexMap<MachineWord, MachineWord>),
    Undefined,
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Boolean(x) => write!(f, "{}", x),
            Value::Bitvector(x) => write!(f, "{}", x),
            Value::Array(_) => write!(f, "virtual memory",),
            Value::Undefined => write!(f, "undefined",),
        }
    }
}

impl Display for MachineWord {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Concrete(x) => write!(f, "{}", x),
        }
    }
}

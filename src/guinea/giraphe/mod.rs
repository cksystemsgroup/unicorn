mod graph;
mod operators;
mod spot;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::unicorn::{Nid, NodeRef};
use egui::{Pos2, Vec2};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

#[allow(unused)]
#[derive(Default, Debug)]
pub struct Giraphe {
    pub(crate) tick: isize,
    pub spot_lookup: HashMap<Nid, Spot>,
    pub spot_list: Vec<Nid>,
    pub leaves: Vec<Nid>,
    pub inputs: Vec<Nid>,
    pub states: Vec<Nid>,
    pub pan: Vec2,
    pub registers: [Option<Nid>; 32],
    pub is_ascii: bool,
    pub input: String,
    pub input_queue: Vec<String>,
}

#[allow(unused)]
#[derive(Debug)]
pub struct Spot {
    tick: isize,
    pub(crate) val_old: Value,
    pub(crate) val_cur: Value,
    pub(crate) origin: NodeRef,
    pub(crate) position: Pos2,
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
    String(String),
    Array(HashMap<MachineWord, MachineWord>),
    Immediate(u64),
    Undefined,
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Boolean(x) => write!(f, "{}", x),
            Value::Bitvector(x) => write!(f, "{}", x),
            Value::String(x) => write!(f, "{}", x),
            Value::Array(_) => write!(f, "virtual memory",),
            Value::Immediate(x) => write!(f, "{}", x),
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

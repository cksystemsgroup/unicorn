mod graph;
mod operators;
mod spot;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::unicorn::NodeRef;
use egui::{Pos2, Vec2};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

#[allow(unused)]
#[derive(Default, Debug)]
pub struct Giraphe {
    tick: usize,
    pub spot_lookup: HashMap<u64, SpotRef>,
    pub spot_list: Vec<SpotRef>,
    pub leaves: Vec<SpotRef>,
    pub inputs: Vec<SpotRef>,
    pub pan: Vec2,
}

#[allow(unused)]
#[derive(Debug, Clone)]
pub struct Spot {
    tick: usize,
    val_old: Value,
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
            Value::Undefined => write!(f, "undefined value",),
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

pub type SpotRef = Rc<RefCell<Spot>>;

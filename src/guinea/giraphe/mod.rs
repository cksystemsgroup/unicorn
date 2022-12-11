mod graph;
mod spot;

use crate::unicorn::NodeRef;
use egui::{Pos2, Vec2};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[allow(unused)]
#[derive(Default, Debug)]
pub struct Giraphe {
    tick: usize,
    pub spot_lookup: HashMap<u64, SpotRef>,
    pub spot_list: Vec<SpotRef>,
    pub leaves: Vec<SpotRef>,
    pub pan: Vec2,
}

#[allow(unused)]
#[derive(Debug, Clone)]
pub struct Spot {
    tick: usize,
    val_old: Value,
    val_cur: Value,
    origin: NodeRef,
    pub(crate) position: Pos2,
}

#[allow(unused)]
#[derive(Debug, Clone)]
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

pub type SpotRef = Rc<RefCell<Spot>>;

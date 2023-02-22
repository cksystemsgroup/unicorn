mod draw;
mod graph;
mod layout;
mod operators;
mod spot;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::unicorn::{Nid, NodeRef};
use egui::Vec2;
use indexmap::IndexMap;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

#[derive(Default, Debug)]
pub(crate) struct Giraphe {
    pub(crate) tick: isize,
    pub(crate) node_lookup: IndexMap<Nid, Spot>,
    pub(crate) roots: Vec<Nid>,
    pub(crate) states: Vec<Nid>,
    pub(crate) node_to_children: IndexMap<Nid, Vec<Nid>>,
    pub(crate) pan: Vec2,
    pub(crate) registers: [Option<Nid>; 32],
    pub(crate) is_ascii: bool,
    pub(crate) input_ascii: String,
    pub(crate) input_number: u8,
    pub(crate) consumed_inputs: Vec<String>,
    pub(crate) layout: Layout,
    pub(crate) in_bad_state: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct Spot {
    tick: isize,
    pub(crate) old_value: Value,
    pub(crate) current_value: Value,
    pub(crate) origin: NodeRef,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub(crate) enum MachineWord {
    Concrete(u64),
    // Symbolic(?),
}

#[derive(Debug, Clone)]
pub(crate) enum Value {
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

#[derive(Eq, PartialEq, Hash, Debug, Copy, Clone)]
pub(crate) enum LayoutNode {
    Real(Nid),
    Dummy(Nid),
}

#[derive(Debug)]
pub(crate) struct Pos {
    x: f32,
    y: f32,
}

impl PartialEq for Pos {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for Pos {}

impl Pos {
    fn key(&self) -> u64 {
        ((self.x.to_bits() as u64) << 32) + self.y.to_bits() as u64
    }

    fn new(x: f32, y: f32) -> Self {
        Self { x, y }
    }
}

impl Hash for Pos {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state)
    }
}

#[derive(Default, Debug)]
pub struct Layout {
    layers: Vec<Vec<LayoutNode>>,
    child_edges: IndexMap<LayoutNode, Vec<LayoutNode>>,
    pub(crate) positions: IndexMap<LayoutNode, Pos>,
    pub(crate) edges_to_its_dummies: IndexMap<(LayoutNode, LayoutNode), Vec<LayoutNode>>,
}

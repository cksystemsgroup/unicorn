use anyhow::Result;
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::ops::Range;
use std::rc::Rc;

//
// Public Interface
//

pub mod bitblasting;
pub mod bitblasting_printer;
pub mod builder;
pub mod memory;
pub mod optimize;
pub mod qubot;
pub mod solver;
pub mod unroller;

pub type Nid = u64;
pub type NodeRef = Rc<RefCell<Node>>;

#[derive(Debug)]
pub enum Node {
    Const {
        nid: Nid,
        sort: NodeType,
        imm: u64,
    },
    Read {
        nid: Nid,
        memory: NodeRef,
        address: NodeRef,
    },
    Write {
        nid: Nid,
        memory: NodeRef,
        address: NodeRef,
        value: NodeRef,
    },
    Add {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Sub {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Mul {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Div {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Rem {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Ult {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Ext {
        nid: Nid,
        from: NodeType,
        value: NodeRef,
    },
    Ite {
        nid: Nid,
        sort: NodeType,
        cond: NodeRef,
        left: NodeRef,
        right: NodeRef,
    },
    Eq {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    And {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Not {
        nid: Nid,
        value: NodeRef,
    },
    State {
        nid: Nid,
        sort: NodeType,
        init: Option<NodeRef>,
        name: Option<String>,
    },
    Next {
        nid: Nid,
        sort: NodeType,
        state: NodeRef,
        next: NodeRef,
    },
    Input {
        nid: Nid,
        sort: NodeType,
        name: String,
    },
    Bad {
        nid: Nid,
        cond: NodeRef,
        name: Option<String>,
    },
    Comment(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum NodeType {
    Bit,
    Word,
    Memory,
    Input1Byte,
    Input2Byte,
    Input3Byte,
    Input4Byte,
    Input5Byte,
    Input6Byte,
    Input7Byte,
}

#[derive(Debug)]
pub struct Model {
    pub lines: Vec<NodeRef>,
    pub sequentials: Vec<NodeRef>,
    pub bad_states_initial: Vec<NodeRef>,
    pub bad_states_sequential: Vec<NodeRef>,
    pub data_range: Range<u64>,
    pub heap_range: Range<u64>,
    pub stack_range: Range<u64>,
    pub memory_size: u64,
}

#[derive(Clone, Debug)]
pub struct HashableNodeRef {
    value: NodeRef,
}

#[rustfmt::skip]
pub fn write_model<W>(model: &Model, mut out: W) -> Result<()>
where
    W: Write,
{
    writeln!(out, "; cksystemsgroup.github.io/monster\n")?;
    writeln!(out,
        "; {} total virtual memory, {} data, {} max heap, {} max stack\n",
        bytesize::ByteSize(model.memory_size).to_string_as(true),
        bytesize::ByteSize(model.data_range.size_hint().0 as u64),
        bytesize::ByteSize(model.heap_range.size_hint().0 as u64),
        bytesize::ByteSize(model.stack_range.size_hint().0 as u64)
    )?;
    writeln!(out, "1 sort bitvec 1 ; Boolean")?;
    writeln!(out, "2 sort bitvec 64 ; 64-bit machine word")?;
    writeln!(out, "3 sort array 2 2 ; 64-bit virtual memory")?;
    writeln!(out, "11 sort bitvec 8 ; 1 byte")?;
    writeln!(out, "12 sort bitvec 16 ; 2 bytes")?;
    writeln!(out, "13 sort bitvec 24 ; 3 bytes")?;
    writeln!(out, "14 sort bitvec 32 ; 4 bytes")?;
    writeln!(out, "15 sort bitvec 40 ; 5 bytes")?;
    writeln!(out, "16 sort bitvec 48 ; 6 bytes")?;
    writeln!(out, "17 sort bitvec 56 ; 7 bytes")?;
    for node in model.lines.iter() {
        match &*node.borrow() {
            Node::Const { nid, sort, imm } =>
                writeln!(out, "{} constd {} {}", nid, get_sort(sort), imm)?,
            Node::Read { nid, memory, address } =>
                writeln!(out, "{} read 2 {} {}", nid, get_nid(memory), get_nid(address))?,
            Node::Write { nid, memory, address, value } =>
                writeln!(out, "{} write 3 {} {} {}", nid, get_nid(memory), get_nid(address), get_nid(value))?,
            Node::Add { nid, left, right } =>
                writeln!(out, "{} add 2 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::Sub { nid, left, right } =>
                writeln!(out, "{} sub 2 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::Mul { nid, left, right } =>
                writeln!(out, "{} mul 2 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::Div { nid, left, right } =>
                writeln!(out, "{} udiv 2 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::Rem { nid, left, right } =>
                writeln!(out, "{} urem 2 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::Ult { nid, left, right } =>
                writeln!(out, "{} ult 1 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::Ext { nid, from, value } =>
                writeln!(out, "{} uext 2 {} {}", nid, get_nid(value), 64 - from.bitsize())?,
            Node::Ite { nid, sort, cond, left, right } =>
                writeln!(out, "{} ite {} {} {} {}", nid, get_sort(sort), get_nid(cond), get_nid(left), get_nid(right))?,
            Node::Eq { nid, left, right } =>
                writeln!(out, "{} eq 1 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::And { nid, left, right } =>
                writeln!(out, "{} and 1 {} {}", nid, get_nid(left), get_nid(right))?,
            Node::Not { nid, value } =>
                writeln!(out, "{} not 1 {}", nid, get_nid(value))?,
            Node::State { nid, sort, init, name } => {
                writeln!(out, "{} state {} {}", nid, get_sort(sort), name.as_deref().unwrap_or("?"))?;
                if let Some(value) = init {
                    writeln!(out, "{} init {} {} {}", nid + 1, get_sort(sort), nid, get_nid(value))?;
                }
            }
            Node::Next { nid, sort, state, next } =>
                writeln!(out, "{} next {} {} {}", nid, get_sort(sort), get_nid(state), get_nid(next))?,
            Node::Input { nid, sort, name } =>
                writeln!(out, "{} input {} {}", nid, get_sort(sort), name)?,
            Node::Bad { nid, cond, name } =>
                writeln!(out, "{} bad {} {}", nid, get_nid(cond), name.as_deref().unwrap_or("?"))?,
            Node::Comment(s) =>
                writeln!(out, "\n; {}\n", s)?,
        }
    }
    writeln!(out, "\n; end of BTOR2 file")?;
    Ok(())
}

//
// Private Implementation
//

pub fn get_nid(node: &NodeRef) -> Nid {
    match *node.borrow() {
        Node::Const { nid, .. } => nid,
        Node::Read { nid, .. } => nid,
        Node::Write { nid, .. } => nid,
        Node::Add { nid, .. } => nid,
        Node::Sub { nid, .. } => nid,
        Node::Mul { nid, .. } => nid,
        Node::Div { nid, .. } => nid,
        Node::Rem { nid, .. } => nid,
        Node::Ult { nid, .. } => nid,
        Node::Ext { nid, .. } => nid,
        Node::Ite { nid, .. } => nid,
        Node::Eq { nid, .. } => nid,
        Node::And { nid, .. } => nid,
        Node::Not { nid, .. } => nid,
        Node::State { nid, .. } => nid,
        Node::Next { nid, .. } => nid,
        Node::Input { nid, .. } => nid,
        Node::Bad { nid, .. } => nid,
        Node::Comment(_) => panic!("has no nid"),
    }
}

fn get_sort(sort: &NodeType) -> Nid {
    match *sort {
        NodeType::Bit => 1,
        NodeType::Word => 2,
        NodeType::Memory => 3,
        NodeType::Input1Byte => 11,
        NodeType::Input2Byte => 12,
        NodeType::Input3Byte => 13,
        NodeType::Input4Byte => 14,
        NodeType::Input5Byte => 15,
        NodeType::Input6Byte => 16,
        NodeType::Input7Byte => 17,
    }
}

impl NodeType {
    fn bitsize(&self) -> usize {
        match *self {
            NodeType::Bit => 1,
            NodeType::Word => 64,
            NodeType::Input1Byte => 8,
            NodeType::Input2Byte => 16,
            NodeType::Input3Byte => 24,
            NodeType::Input4Byte => 32,
            NodeType::Input5Byte => 40,
            NodeType::Input6Byte => 48,
            NodeType::Input7Byte => 56,
            _ => panic!("unknown bitsize"),
        }
    }
}

impl Eq for HashableNodeRef {}

impl From<NodeRef> for HashableNodeRef {
    fn from(node: NodeRef) -> Self {
        Self { value: node }
    }
}

impl Hash for HashableNodeRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

impl PartialEq for HashableNodeRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}

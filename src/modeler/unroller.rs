use crate::modeler::{HashableNodeRef, Model, Nid, Node, NodeRef};
use log::debug;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

//
// Public Interface
//

pub fn unroll_model(model: &mut Model, n: usize) {
    debug!("Unrolling iteration #{} from sequential model ...", n);
    let mut replacements = Vec::<(NodeRef, NodeRef)>::new();
    let mut model_unroller = ModelUnroller::new(n);
    for sequential in &model.sequentials {
        if let Node::Next { state, next, .. } = &*sequential.borrow() {
            let unrolled = model_unroller.unroll(next);
            replacements.push((state.clone(), unrolled));
        } else {
            panic!("expecting 'Next' node here");
        }
    }
    for bad_state in &model.bad_states_sequential {
        let bad_copy = model_unroller.unroll(bad_state);
        model.bad_states_initial.push(bad_copy);
    }
    for (state, new_init) in replacements {
        if let Node::State { ref mut init, .. } = *state.borrow_mut() {
            *init = Some(new_init);
        } else {
            panic!("expecting 'State' node here");
        }
    }
}

pub fn prune_model(model: &mut Model) {
    debug!("Pruning sequential portion of unrolled model ...");
    model.sequentials.clear();
    model.bad_states_sequential.clear();
}

pub fn renumber_model(model: &mut Model) {
    debug!("Renumbering nodes in unrolled model ...");
    let mut model_renumberer = ModelRenumberer::new();
    let s = "Model was renumbered, it will be hard to read.";
    let comment = Rc::new(RefCell::new(Node::Comment(s.to_string())));
    model_renumberer.lines.push(comment);
    for sequential in &model.sequentials {
        model_renumberer.visit(sequential)
    }
    for bad_state in &model.bad_states_initial {
        model_renumberer.visit(bad_state)
    }
    for bad_state in &model.bad_states_sequential {
        model_renumberer.visit(bad_state)
    }
    model.lines = model_renumberer.lines;
}

//
// Private Implementation
//

struct ModelRenumberer {
    current_nid: Nid,
    marks: HashSet<HashableNodeRef>,
    lines: Vec<NodeRef>,
}

impl ModelRenumberer {
    fn new() -> Self {
        Self {
            current_nid: 10000000,
            marks: HashSet::new(),
            lines: Vec::new(),
        }
    }

    fn add_line(&mut self, node: &NodeRef) {
        self.lines.push(node.clone());
    }

    fn next_nid(&mut self, nid: &mut Nid) {
        *nid = self.current_nid;
        self.current_nid += 1;
    }

    fn visit(&mut self, node: &NodeRef) {
        let key = HashableNodeRef::from(node.clone());
        if !self.marks.contains(&key) {
            self.process(node);
            self.add_line(node);
            self.marks.insert(key);
        }
    }

    #[rustfmt::skip]
    fn process(&mut self, node: &NodeRef) {
        match *node.borrow_mut() {
            Node::Const { ref mut nid, .. } => {
                self.next_nid(nid);
            }
            Node::Read { ref mut nid, ref memory, ref address, .. } => {
                self.visit(memory);
                self.visit(address);
                self.next_nid(nid);
            }
            Node::Write { ref mut nid, ref memory, ref address, ref value, .. } => {
                self.visit(memory);
                self.visit(address);
                self.visit(value);
                self.next_nid(nid);
            }
            Node::Add { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Sub { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Mul { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Div { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Rem { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Ult { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Ext { ref mut nid, ref value, .. } => {
                self.visit(value);
                self.next_nid(nid);
            }
            Node::Ite { ref mut nid, ref cond, ref left, ref right, .. } => {
                self.visit(cond);
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Eq { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::And { ref mut nid, ref left, ref right, .. } => {
                self.visit(left);
                self.visit(right);
                self.next_nid(nid);
            }
            Node::Not { ref mut nid, ref value, .. } => {
                self.visit(value);
                self.next_nid(nid);
            }
            Node::State { ref mut nid, init: None, .. } => {
                self.next_nid(nid);
            }
            Node::State { ref mut nid, init: Some(ref init), .. } => {
                self.visit(init);
                self.next_nid(nid);
                self.current_nid += 1;
            }
            Node::Next { ref mut nid, ref state, ref next, .. } => {
                self.visit(state);
                self.visit(next);
                self.next_nid(nid);
            }
            Node::Input { ref mut nid, .. } => {
                self.next_nid(nid);
            }
            Node::Bad { ref mut nid, ref cond, .. } => {
                self.visit(cond);
                self.next_nid(nid);
            }
            Node::Comment(_) => panic!("cannot renumber"),
        }
    }
}

struct ModelUnroller {
    current_iteration: usize,
    copies: HashMap<HashableNodeRef, NodeRef>,
}

impl ModelUnroller {
    fn new(n: usize) -> Self {
        Self {
            current_iteration: n,
            copies: HashMap::new(),
        }
    }

    fn unroll(&mut self, node: &NodeRef) -> NodeRef {
        let key = HashableNodeRef::from(node.clone());
        self.copies.get(&key).cloned().unwrap_or_else(|| {
            let value = self.deep_copy(node);
            assert!(!self.copies.contains_key(&key));
            self.copies.insert(key, value.clone());
            value
        })
    }

    #[rustfmt::skip]
    fn deep_copy(&mut self, node: &NodeRef) -> NodeRef {
        match &*node.borrow() {
            Node::Const { .. } => node.clone(),
            Node::Read { memory, address, .. } => {
                Rc::new(RefCell::new(Node::Read {
                    nid: 0,
                    memory: self.unroll(memory),
                    address: self.unroll(address),
                }))
            }
            Node::Write { memory, address, value, .. } => {
                Rc::new(RefCell::new(Node::Write {
                    nid: 0,
                    memory: self.unroll(memory),
                    address: self.unroll(address),
                    value: self.unroll(value),
                }))
            }
            Node::Add { left, right, .. } => {
                Rc::new(RefCell::new(Node::Add {
                    nid: 0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Sub { left, right, .. } => {
                Rc::new(RefCell::new(Node::Sub {
                    nid: 0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Mul { left, right, .. } => {
                Rc::new(RefCell::new(Node::Mul {
                    nid: 0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Div { left, right, .. } => {
                Rc::new(RefCell::new(Node::Div {
                    nid: 0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Rem { left, right, .. } => {
                Rc::new(RefCell::new(Node::Rem {
                    nid: 0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Ult { left, right, .. } => {
                Rc::new(RefCell::new(Node::Ult {
                    nid: 0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Ext { from, value, .. } => {
                Rc::new(RefCell::new(Node::Ext {
                    nid: 0,
                    from: from.clone(),
                    value: self.unroll(value),
                }))
            }
            Node::Ite { sort, cond, left, right, .. } => {
                Rc::new(RefCell::new(Node::Ite {
                    nid: 0,
                    sort: sort.clone(),
                    cond: self.unroll(cond),
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Eq { left, right, .. } => {
                Rc::new(RefCell::new(Node::Eq {
                    nid:0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::And { left, right, .. } => {
                Rc::new(RefCell::new(Node::And {
                    nid: 0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Not { value, .. } => {
                Rc::new(RefCell::new(Node::Not {
                    nid: 0,
                    value: self.unroll(value),
                }))
            }
            Node::Input { sort, name, .. } => {
                let new_name = format!("{}[n={}]", name, self.current_iteration);
                Rc::new(RefCell::new(Node::State {
                    nid: 0,
                    sort: sort.clone(),
                    init: None,
                    name: Some(new_name),
                }))
            }
            Node::Bad { cond, name, .. } => {
                let name = name.as_deref().unwrap_or("?");
                let new_name = format!("{}[n={}]", name, self.current_iteration);
                Rc::new(RefCell::new(Node::Bad {
                    nid: 0,
                    cond: self.unroll(cond),
                    name: Some(new_name),
                }))
            }
            Node::State { init: Some(init), .. } => init.clone(),
            Node::State { init: None, .. } => panic!("uninitialized"),
            Node::Next { .. } => panic!("should be unreachable"),
            Node::Comment(_) => panic!("cannot copy"),
        }
    }
}

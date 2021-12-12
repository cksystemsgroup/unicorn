use crate::modeler::{Model, Node, NodeRef};
use log::debug;
use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

//
// Public Interface
//

pub fn unroll_model(model: &mut Model, n: usize) {
    debug!("Unrolling iteration #{} from sequential model ...", n);
    let mut replacements = Vec::<(NodeRef, NodeRef)>::new();
    let mut model_unroller = ModelUnroller::new();
    for sequential in &model.sequentials {
        if let Node::Next { state, next, .. } = &*sequential.borrow() {
            let unrolled = model_unroller.unroll(next);
            replacements.push((state.clone(), unrolled));
        } else {
            panic!("expecting 'Next' node here");
        }
    }
    for (state, new_init) in replacements {
        if let Node::State { ref mut init, .. } = *state.borrow_mut() {
            *init = Some(new_init);
        } else {
            panic!("expecting 'State' node here");
        }
    }
}

//
// Private Implementation
//

struct HashableNodeRef {
    value: NodeRef,
}

impl Eq for HashableNodeRef {}

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

struct ModelUnroller {
    copies: HashMap<HashableNodeRef, NodeRef>,
}

impl ModelUnroller {
    fn new() -> Self {
        Self {
            copies: HashMap::new(),
        }
    }

    fn unroll(&mut self, node: &NodeRef) -> NodeRef {
        let key = HashableNodeRef {
            value: node.clone(),
        };
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
                    nid:0,
                    memory: self.unroll(memory),
                    address: self.unroll(address),
                }))
            }
            Node::Write { memory, address, value, .. } => {
                Rc::new(RefCell::new(Node::Write {
                    nid:0,
                    memory: self.unroll(memory),
                    address: self.unroll(address),
                    value: self.unroll(value),
                }))
            }
            Node::Add { left, right, .. } => {
                Rc::new(RefCell::new(Node::Add {
                    nid:0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Sub { left, right, .. } => {
                Rc::new(RefCell::new(Node::Sub {
                    nid:0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Rem { left, right, .. } => {
                Rc::new(RefCell::new(Node::Rem {
                    nid:0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Ite { sort, cond, left, right, .. } => {
                Rc::new(RefCell::new(Node::Ite {
                    nid:0,
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
                    nid:0,
                    left: self.unroll(left),
                    right: self.unroll(right),
                }))
            }
            Node::Not { value, .. } => {
                Rc::new(RefCell::new(Node::Not {
                    nid:0,
                    value: self.unroll(value),
                }))
            }
            Node::State { init: Some(init), .. } => init.clone(),
            Node::State { init: None, .. } => panic!("uninitialized"),
            Node::Next { .. } => panic!("should be unreachable"),
            Node::Comment(_) => panic!("cannot copy"),
        }
    }
}

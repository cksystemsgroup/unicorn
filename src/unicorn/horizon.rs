use crate::unicorn::{Node, Model};
use log::warn;

//
// Public Interface
//

pub fn print_reasoning_horizon(model: &mut Model) {
    let v: Option<String>;
    v = match &*model.bad_states_initial[0].borrow() {
        Node::Bad { name, ..} => name.clone(),
        _ => None
    };
    
    let bad_state = v.as_ref().expect("Bad state must have an unrolling depth");
    warn!("(Initial) Bad state '{}' is satisfiable.", bad_state);
}
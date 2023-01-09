use crate::unicorn::{Node, Model};
use log::warn;

//
// Public Interface
//

pub fn print_reasoning_horizon(model: &mut Model, depth: usize, stride: bool) {
    let v: Option<String>;
    v = match &*model.bad_states_initial[0].borrow() {
        Node::Bad { name, ..} => name.clone(),
        _ => None
    };

    let ss = v.as_ref().expect("Bad state must have an unrolling depth");
    if let (Some(start), Some(end)) = (ss.find("[n="), ss.find("]")) {
        if let (reason, Ok(remainder)) = (ss[..start].to_string(), ss[start+"[n=".len()..end].to_string().parse::<usize>()) {
            warn!(
                "(Initial) Bad state '{}[n={:#?}]' is satisfiable.",
                reason,
                if stride { (depth - 1) + remainder } else { remainder }
            );
        }
    
    }
}
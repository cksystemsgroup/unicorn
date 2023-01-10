use crate::{unicorn::{Model, Node, NodeRef, NodeType}, emulate, engine};
use log::{debug, trace, warn};
use riscu::Register;
use emulate::{EmulatorState, EmulatorValue};
use engine::system::NUMBER_OF_REGISTERS;

//
// Public Interface
//

pub fn load_model_into_emulator(emulator: &mut EmulatorState, model: &Model) {
    debug!("Loading initial part of model into emulator ...");
    for sequential in &model.sequentials {
        if let Node::Next { state, .. } = &*sequential.borrow() {
            if let Node::State { init, name, .. } = &*state.borrow() {
                let name = name.as_ref().expect("must exist");
                let init = init.as_ref().expect("must exist");
                if let Some(reg) = name_to_register(name) {
                    let val = to_emulator_value(init);
                    trace!("setting {:?} <- {:#x}", reg, val);
                    emulator.set_reg(reg, val);
                    continue;
                }
                if let Some(pc) = name_to_pc_value(name) {
                    let val = to_emulator_value(init);
                    assert!(val == 0 || val == 1);
                    if val == 1 {
                        trace!("setting PC <- {:#x}", pc);
                        emulator.pc_set(pc);
                    }
                    continue;
                }
                if name == "bump-pointer" {
                    let val = to_emulator_value(init);
                    trace!("setting BRK <- {:#x}", val);
                    emulator.set_program_break(val);
                    continue;
                }
                if name == "virtual-memory" {
                    perform_stores(emulator, init);
                    continue;
                }
                if name.starts_with("kernel-mode") {
                    let val = to_emulator_value(init);
                    assert!(val == 0 || val == 1);
                    if val == 1 {
                        warn!("Model in kernel mode '{}', emulation will fail!", name);
                        panic!("model in kernel mode");
                    }
                    continue;
                }
                panic!("unhandled state: {}", name);
            } else {
                panic!("expecting 'State' node here");
            }
        } else {
            panic!("expecting 'Next' node here");
        }
    }
}

//
// Private Implementation
//

// TODO: Move to public portion of file.
pub fn name_to_register(name: &str) -> Option<Register> {
    for r in 1..NUMBER_OF_REGISTERS {
        let reg = Register::from(r as u32);
        if name == format!("{:?}", reg) {
            return Some(reg);
        }
    }
    None
}

// TODO: Move to public portion of file.
pub fn name_to_pc_value(name: &str) -> Option<EmulatorValue> {
    let value = name.strip_prefix("pc=0x")?;
    u64::from_str_radix(value, 16).ok()
}

fn to_emulator_value(node: &NodeRef) -> EmulatorValue {
    match &*node.borrow() {
        Node::Const { imm, .. } => *imm,
        _ => panic!("unexpected node: {:?}", node),
    }
}

#[rustfmt::skip]
fn perform_stores(emulator: &mut EmulatorState, node: &NodeRef) {
    match &*node.borrow() {
        Node::Write { memory, address, value, .. } => {
            perform_stores(emulator, memory);
            let adr = to_emulator_value(address);
            let val = to_emulator_value(value);
            trace!("storing mem[{:#x}] <- {:#x}", adr, val);
            emulator.set_mem(adr, val);
        }
        Node::State { sort: NodeType::Memory, init: None, .. } => (),
        _ => panic!("unexpected node: {:?}", node),
    }
}

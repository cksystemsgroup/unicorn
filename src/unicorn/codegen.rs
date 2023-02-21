use crate::unicorn::emulate_loader::{name_to_pc_value, name_to_register};
use crate::unicorn::{Model, Node, NodeRef, NodeType};
use crate::{disassemble, emulate, engine};
use byteorder::{ByteOrder, LittleEndian};
use disassemble::Disassembly;
use emulate::{EmulatorState, EmulatorValue};
use engine::system::NUMBER_OF_REGISTERS;
use log::{debug, info, trace, warn};
use riscu::{decode, DecodedProgram, Instruction, Program, ProgramSegment, Register};
use unicorn::disassemble::Disassembly;
use unicorn::emulate::{EmulatorState, EmulatorValue};
use unicorn::engine::system::NUMBER_OF_REGISTERS;

//
// Public Interface
//

pub fn compile_model_into_program(emulator: &mut EmulatorState, model: &Model, original: &Program) {
    debug!("Compiling initial part of model into program ...");
    let code_start = determine_start_of_new_code(original);
    let target_state = translate_model_into_target_state(model);
    let mut codegen = CodeGenerator::new(emulator, &target_state, code_start);
    codegen.compile_code_to_enter_target_state();
    codegen.patch_emulator_state();
    codegen.disassemble();
}

//
// Private Implementation
//

const INSTRUCTION_SIZE: u64 = riscu::INSTRUCTION_SIZE as u64;
const WORD_SIZE: u64 = riscu::WORD_SIZE as u64;

struct CodeGenerator<'a> {
    source_state: &'a mut EmulatorState,
    target_state: &'a SymbolicState,
    code: Vec<u8>,
    code_start: u64,
}

struct SymbolicState {
    // This is the relevant part in `EmulatorState`:
    //   - registers: Vec<EmulatorValue>,
    //   - memory: Vec<u8>,
    //   - program_counter: EmulatorValue,
    //   - program_break: EmulatorValue,
    registers: Vec<Option<NodeRef>>,
    memory: Vec<Option<NodeRef>>,
    program_counter: Vec<(NodeRef, EmulatorValue)>,
    program_break: Option<NodeRef>,
}

fn determine_start_of_new_code(original: &Program) -> u64 {
    original.code.address + original.code.content.len() as u64 * INSTRUCTION_SIZE
}

fn translate_model_into_target_state(model: &Model) -> SymbolicState {
    let mut registers = vec![None; NUMBER_OF_REGISTERS];
    let mut memory = vec![None; model.memory_size as usize];
    let mut program_counter = vec![];
    let mut program_break = None;
    for sequential in &model.sequentials {
        if let Node::Next { state, .. } = &*sequential.borrow() {
            if let Node::State { init, name, .. } = &*state.borrow() {
                let name = name.as_ref().expect("must exist");
                let init = init.as_ref().expect("must exist");
                if let Some(reg) = name_to_register(name) {
                    registers[reg as usize] = Some(init.clone());
                    continue;
                }
                if let Some(pc) = name_to_pc_value(name) {
                    program_counter.push((init.clone(), pc));
                    continue;
                }
                if name == "bump-pointer" {
                    program_break.replace(init.clone());
                    continue;
                }
                if name == "virtual-memory" {
                    translate_stores_to_memory(init, &mut memory);
                    continue;
                }
                if name.starts_with("kernel-mode") {
                    let val = translate_to_constant(init).expect("constant");
                    assert!(val == 0 || val == 1);
                    if val == 1 {
                        warn!("Model in kernel mode '{}', compilation will fail!", name);
                        panic!("model in kernel mode");
                    }
                    continue;
                }
                if name.starts_with("dynamic-dispatch-on") {
                    // Nothing to do here.
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
    SymbolicState {
        registers,
        memory,
        program_counter,
        program_break,
    }
}

#[rustfmt::skip]
fn translate_stores_to_memory(node: &NodeRef, flat_memory: &mut Vec<Option<NodeRef>>) {
    match &*node.borrow() {
        Node::Write { memory, address, value, .. } => {
            translate_stores_to_memory(memory, flat_memory);
            let adr = translate_to_constant(address).expect("constant");
            flat_memory[adr as usize] = Some(value.clone());
        }
        Node::State { sort: NodeType::Memory, init: None, .. } => (),
        _ => panic!("unexpected node: {:?}", node),
    }
}

fn translate_to_constant(node: &NodeRef) -> Option<EmulatorValue> {
    match &*node.borrow() {
        Node::Const { imm, .. } => Some(*imm),
        _ => None,
    }
}

impl<'a> CodeGenerator<'a> {
    fn new(source: &'a mut EmulatorState, target: &'a SymbolicState, code_start: u64) -> Self {
        Self {
            source_state: source,
            target_state: target,
            code: Vec::new(),
            code_start,
        }
    }

    fn disassemble(&self) {
        let code = ProgramSegment {
            address: self.code_start,
            content: self.code.clone(),
        };
        let data = ProgramSegment {
            address: 0,
            content: vec![],
        };
        let decoded = DecodedProgram { code, data };
        let disassembly = Disassembly::new(decoded);
        info!("dissasembly of added code:\n{}", disassembly);
    }

    /// Append an instruction to the encoded code segment
    fn push_instruction(&mut self, instr: Instruction) {
        self.code.extend_from_slice(&u32::from(instr).to_le_bytes());
    }

    fn emit_addi(&mut self, rd: Register, rs1: Register, imm: i32) {
        if rd == rs1 && imm == 0 {
            return; // skip a nop
        }

        self.push_instruction(Instruction::new_addi(rd, rs1, imm));
    }

    fn emit_jal(&mut self, rd: Register, imm: i32) {
        self.push_instruction(Instruction::new_jal(rd, imm));
    }

    fn emit_lui(&mut self, rd: Register, imm: i32) {
        self.push_instruction(Instruction::new_lui(rd, imm));
    }

    fn emit_sd(&mut self, rs1: Register, rs2: Register, imm: i32) {
        self.push_instruction(Instruction::new_sd(rs1, rs2, imm));
    }

    fn load_integer(&mut self, reg: Register, imm: u64) {
        let value = imm as i64;
        let small_range = -(1i64 << 11)..(1i64 << 11);
        let medium_range = -(1i64 << 31)..(1i64 << 31);
        if small_range.contains(&value) {
            // -2^11 <= value < 2^11
            self.emit_addi(reg, Register::Zero, value as i32);
        } else if medium_range.contains(&value) {
            // -2^31 <= value < -2^11 or 2^11 <= value < 2^31
            let upper = (value >> 12) as i32;
            let lower = ((value as i32) << 20) >> 20;
            self.emit_lui(reg, upper);
            self.emit_addi(reg, reg, lower);
        } else {
            unimplemented!("big integers not implemented")
        }
    }

    fn perform_store(&mut self, adr: EmulatorValue, val: &NodeRef) {
        self.process(val, Register::T6);
        self.load_integer(Register::T5, adr);
        self.emit_sd(Register::T5, Register::T6, 0);
    }

    fn perform_jump(&mut self, target_pc: EmulatorValue) {
        assert!(target_pc != self.source_state.get_program_counter());
        let origin_pc = self.code_start + self.code.len() as u64 * INSTRUCTION_SIZE;
        let offset = u64::wrapping_sub(target_pc, origin_pc) as i32;
        self.emit_jal(Register::Zero, offset);
    }

    fn visit(&mut self, node: &NodeRef, reg: Register) {
        // TODO: Ensure each node is only processed once.
        self.process(node, reg);
    }

    #[rustfmt::skip]
    fn process(&mut self, node: &NodeRef, reg: Register) {
        match &*node.borrow() {
            Node::Const { imm, .. } => {
                self.load_integer(reg, *imm);
            }
            _ => panic!("not implemented: {:?}", node),
        }
    }

    fn compile_code_to_enter_target_state(&mut self) {
        if let Some(brk) = &self.target_state.program_break {
            let brk_value = translate_to_constant(brk).expect("constant");
            assert!(brk_value == self.source_state.get_program_break());
        }
        for (a, node) in self.target_state.memory.iter().enumerate() {
            if let Some(node) = node {
                let adr = a as EmulatorValue;
                if let Some(val) = translate_to_constant(node) {
                    if val == self.source_state.get_mem(adr) {
                        trace!("skipping mem[{:#x}], it is redundant", adr);
                        continue;
                    }
                }
                trace!("storing mem[{:#x}] <- {:?}", adr, node);
                self.perform_store(adr, node);
            }
        }
        for (r, node) in self.target_state.registers.iter().enumerate() {
            if let Some(node) = node {
                let reg = Register::from(r as u32);
                if let Some(val) = translate_to_constant(node) {
                    if val == self.source_state.get_reg(reg) {
                        trace!("skipping {:?}, it is redundant", reg);
                        continue;
                    }
                }
                trace!("setting {:?} <- {:?}", reg, node);
                self.visit(node, reg);
            }
        }
        for (cond, pc) in self.target_state.program_counter.iter() {
            if let Some(cond) = translate_to_constant(cond) {
                assert!(cond == 0 || cond == 1, "must be bit");
                if cond == 1 {
                    self.perform_jump(*pc);
                    break; // only one
                }
                continue;
            }
            unimplemented!("dynamic program counter");
        }
    }

    fn patch_instruction(&mut self, pc: u64, instr: Instruction) {
        let word_address = (pc / WORD_SIZE) * WORD_SIZE;
        let word_offset = pc as usize % riscu::WORD_SIZE;
        let encoded_instr: u32 = instr.into();
        trace!(
            "patching mem[{:#x}+{}] <- {:#010x} / {:?}",
            word_address,
            word_offset,
            encoded_instr,
            instr
        );
        let old_word = self.source_state.get_mem(word_address);
        let mut bytes = old_word.to_le_bytes();
        LittleEndian::write_u32(&mut bytes[word_offset..word_offset + 4], encoded_instr);
        let new_word = u64::from_le_bytes(bytes);
        self.source_state.set_mem(word_address, new_word);
    }

    fn patch_entry_jump(&mut self) {
        let target_pc = self.code_start;
        let entry_pc = self.source_state.get_program_counter();
        let offset = u64::wrapping_sub(target_pc, entry_pc) as i32;
        let jump = Instruction::new_jal(Register::Zero, offset);
        self.patch_instruction(entry_pc, jump)
    }

    fn patch_emulator_state(&mut self) {
        self.patch_entry_jump();
        for i in 0..self.code.len() {
            let instr =
                decode(LittleEndian::read_u32(&self.code[i..i + 4])).expect("valid instruction");
            // FIXME: does this code assume u32 alignment? Is the assumption valid?
            let pc = self.code_start + i as u64 * INSTRUCTION_SIZE;
            self.patch_instruction(pc, instr);
        }
    }
}

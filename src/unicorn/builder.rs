use crate::unicorn::{Model, Nid, Node, NodeRef, NodeType};
use anyhow::{Context, Result};
use byteorder::{ByteOrder, LittleEndian};
use log::{debug, trace, warn};
use riscu::{decode, types::*, Instruction, Program, Register};
use std::cell::RefCell;
use std::collections::HashMap;
use std::mem::size_of;
use std::ops::Range;
use std::rc::Rc;
use unicorn::engine::system::{prepare_unix_stack, SyscallId, NUMBER_OF_REGISTERS};
use unicorn::util::next_multiple_of;

//
// Public Interface
//

pub fn generate_model(
    program: &Program,
    memory_size: u64,
    max_heap: u32,
    max_stack: u32,
    argv: &[String],
) -> Result<Model> {
    trace!("Program: {:?}", program);
    let mut builder = ModelBuilder::new(memory_size, max_heap, max_stack);
    builder.generate_model(program, argv)?;
    Ok(builder.finalize())
}

//
// Private Implementation
//

const INSTRUCTION_SIZE: u64 = riscu::INSTRUCTION_SIZE as u64;
const PAGE_SIZE: u64 = unicorn::engine::system::PAGE_SIZE as u64;
const WORD_SIZE_MASK: u64 = riscu::WORD_SIZE as u64 - 1;
const BITS_PER_BYTE: u64 = 8;

// TODO: Add implementation of all syscalls.
// TODO: Fix initialization of `current_nid` based on binary size.
// TODO(test): Test model by adding a poor-man's type-checker.
// TODO(test): Test builder on existing samples automatically.
struct ModelBuilder {
    lines: Vec<NodeRef>,
    sequentials: Vec<NodeRef>,
    bad_states: Vec<NodeRef>,
    pc_flags: HashMap<u64, NodeRef>,       // maps PC -> PC-Flag
    control_in: HashMap<u64, Vec<InEdge>>, // maps PC -> [InEdge]
    dynamic_flags: Vec<NodeRef>,           // maps Register -> Dispatch-Flag
    dynamic: Vec<Vec<DynDispatch>>,        // maps Register -> [DynDispatch]
    zero_bit: NodeRef,
    one_bit: NodeRef,
    zero_word: NodeRef,
    kernel_mode: NodeRef,
    kernel_not: NodeRef,
    register_nodes: Vec<NodeRef>,
    register_flow: Vec<NodeRef>,
    memory_node: NodeRef,
    memory_flow: NodeRef,
    division_flow: NodeRef,
    remainder_flow: NodeRef,
    access_flow: NodeRef,
    ecall_flow: NodeRef,
    memory_size: u64,
    max_heap_size: u64,
    max_stack_size: u64,
    data_range: Range<u64>,
    heap_range: Range<u64>,
    stack_range: Range<u64>,
    current_nid: Nid,
    pc: u64,
}

struct InEdge {
    from_instruction: FromInstruction,
    from_address: u64,
    condition: Option<NodeRef>,
}

struct DynDispatch {
    dispatch_address: u64,
}

enum FromInstruction {
    Regular,    // fall-thru from regular instruction, or jump target (i.e. jal)
    Branch,     // target of conditional branch (e.g. beq, bne, ...)
    SystemCall, // return from system call (i.e. ecall)
}

impl ModelBuilder {
    fn new(memory_size: u64, max_heap: u32, max_stack: u32) -> Self {
        let dummy_node = Rc::new(RefCell::new(Node::Comment("dummy".to_string())));
        Self {
            lines: Vec::new(),
            sequentials: Vec::new(),
            bad_states: Vec::new(),
            pc_flags: HashMap::new(),
            control_in: HashMap::new(),
            dynamic_flags: Vec::with_capacity(NUMBER_OF_REGISTERS - 1),
            dynamic: Vec::with_capacity(NUMBER_OF_REGISTERS - 1),
            zero_bit: dummy_node.clone(),
            one_bit: dummy_node.clone(),
            zero_word: dummy_node.clone(),
            kernel_mode: dummy_node.clone(),
            kernel_not: dummy_node.clone(),
            register_nodes: Vec::with_capacity(NUMBER_OF_REGISTERS),
            register_flow: Vec::with_capacity(NUMBER_OF_REGISTERS - 1),
            memory_node: dummy_node.clone(),
            memory_flow: dummy_node.clone(),
            division_flow: dummy_node.clone(),
            remainder_flow: dummy_node.clone(),
            access_flow: dummy_node.clone(),
            ecall_flow: dummy_node,
            memory_size,
            max_heap_size: max_heap as u64 * size_of::<u64>() as u64,
            max_stack_size: max_stack as u64 * size_of::<u64>() as u64,
            data_range: 0..0,
            heap_range: 0..0,
            stack_range: 0..0,
            current_nid: 0,
            pc: 0,
        }
    }

    fn finalize(self) -> Model {
        Model {
            lines: self.lines,
            sequentials: self.sequentials,
            bad_states_initial: Vec::new(),
            bad_states_sequential: self.bad_states,
            data_range: self.data_range,
            heap_range: self.heap_range,
            stack_range: self.stack_range,
            memory_size: self.memory_size,
        }
    }

    fn pc_add(&self, imm: u64) -> u64 {
        self.pc.wrapping_add(imm)
    }

    fn pc_flag(&self) -> NodeRef {
        self.pc_flags[&self.pc].clone()
    }

    fn reg_node(&self, reg: Register) -> NodeRef {
        self.register_nodes[reg as usize].clone()
    }

    fn reg_flow(&self, reg: Register) -> NodeRef {
        assert!(reg != Register::Zero);
        self.register_flow[reg as usize - 1].clone()
    }

    fn reg_flow_update(&mut self, reg: Register, node: NodeRef) {
        assert!(reg != Register::Zero);
        self.register_flow[reg as usize - 1] = node;
    }

    fn reg_flow_ite(&mut self, reg: Register, node: NodeRef) {
        let ite_node = self.new_ite(self.pc_flag(), node, self.reg_flow(reg), NodeType::Word);
        self.reg_flow_update(reg, ite_node);
    }

    fn dynamic_flag(&self, reg: Register) -> NodeRef {
        assert!(reg != Register::Zero, "dispatch on zero");
        self.dynamic_flags[reg as usize - 1].clone()
    }

    // Returns the list of registers on which dynamic dispatches are
    // performed anywhere in the program. This is just an optimization,
    // returning a list of all registers would be equally valid here.
    fn dynamic_dispatches(&self) -> Vec<Register> {
        self.dynamic
            .iter()
            .enumerate()
            .filter(|(_, v)| !v.is_empty())
            .map(|(r, _)| Register::from(r as u32 + 1))
            .collect()
    }

    fn add_node(&mut self, node_data: Node) -> NodeRef {
        let node = Rc::new(RefCell::new(node_data));
        self.lines.push(node.clone());
        self.current_nid += 1;
        node
    }

    fn new_const(&mut self, imm: u64) -> NodeRef {
        self.add_node(Node::Const {
            nid: self.current_nid,
            sort: NodeType::Word,
            imm,
        })
    }

    fn new_read(&mut self, address: NodeRef) -> NodeRef {
        self.add_node(Node::Read {
            nid: self.current_nid,
            memory: self.memory_node.clone(),
            address,
        })
    }

    fn new_write(&mut self, address: NodeRef, value: NodeRef) -> NodeRef {
        self.add_node(Node::Write {
            nid: self.current_nid,
            memory: self.memory_node.clone(),
            address,
            value,
        })
    }

    fn new_add(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Add {
            nid: self.current_nid,
            left,
            right,
        })
    }

    fn new_sub(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Sub {
            nid: self.current_nid,
            left,
            right,
        })
    }

    fn new_mul(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Mul {
            nid: self.current_nid,
            left,
            right,
        })
    }

    fn new_divu(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Divu {
            nid: self.current_nid,
            left,
            right,
        })
    }

    fn new_div(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Div {
            nid: self.current_nid,
            left,
            right,
        })
    }

    fn new_rem(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Rem {
            nid: self.current_nid,
            left,
            right,
        })
    }

    fn new_ult(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Ult {
            nid: self.current_nid,
            left,
            right,
        })
    }

    // We represent `ugt(a, b)` as `ult(b, a)` instead.
    fn new_ugt(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.new_ult(right, left)
    }

    // We represent `ulte(a, b)` as `not(ult(b, a))` instead.
    fn new_ulte(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        let ult_node = self.new_ult(right, left);
        self.new_not_bit(ult_node)
    }

    // We represent `ugte(a, b)` as `not(ult(a, b))` instead.
    fn new_ugte(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        let ult_node = self.new_ult(left, right);
        self.new_not_bit(ult_node)
    }

    // We represent `slt(a, b)` as `ult(add(a, 2^63), add(b, 2^63))` instead.
    fn new_slt(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        let bias = self.new_const(1 << 63);
        let left_biased = self.new_add(left, bias.clone());
        let right_biased = self.new_add(right, bias);
        self.new_ult(left_biased, right_biased)
    }

    // We represent `sgte(a, b)` as `not(slt(a, b))` instead.
    fn new_sgte(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        let slt_node = self.new_slt(left, right);
        self.new_not_bit(slt_node)
    }

    fn new_ite(&mut self, cond: NodeRef, left: NodeRef, right: NodeRef, sort: NodeType) -> NodeRef {
        self.add_node(Node::Ite {
            nid: self.current_nid,
            sort,
            cond,
            left,
            right,
        })
    }

    fn new_eq(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Eq {
            nid: self.current_nid,
            left,
            right,
        })
    }

    // We represent `neq(a, b)` as `not(eq(a, b))` instead.
    fn new_neq(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        let eq_node = self.new_eq(left, right);
        self.new_not_bit(eq_node)
    }

    fn new_and_bit(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::And {
            nid: self.current_nid,
            sort: NodeType::Bit,
            left,
            right,
        })
    }

    fn new_and_word(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::And {
            nid: self.current_nid,
            sort: NodeType::Word,
            left,
            right,
        })
    }

    // We represent `or(a, b)` as `not(and(not(a), not(b)))` instead.
    fn new_or(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        let not_left_node = self.new_not_word(left);
        let not_right_node = self.new_not_word(right);
        let and_node = self.new_and_word(not_left_node, not_right_node);
        self.new_not_word(and_node)
    }

    // We represent `xor(a, b)` as `sub(or(a, b), and(a, b))` instead.
    fn new_xor(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        let or_node = self.new_or(left.clone(), right.clone());
        let and_node = self.new_and_word(left, right);
        self.new_sub(or_node, and_node)
    }

    fn new_not_bit(&mut self, value: NodeRef) -> NodeRef {
        self.add_node(Node::Not {
            nid: self.current_nid,
            sort: NodeType::Bit,
            value,
        })
    }

    fn new_not_word(&mut self, value: NodeRef) -> NodeRef {
        self.add_node(Node::Not {
            nid: self.current_nid,
            sort: NodeType::Word,
            value,
        })
    }

    fn new_sll(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Sll {
            nid: self.current_nid,
            left,
            right,
        })
    }

    fn new_srl(&mut self, left: NodeRef, right: NodeRef) -> NodeRef {
        self.add_node(Node::Srl {
            nid: self.current_nid,
            left,
            right,
        })
    }

    // We represent `sra(a, n)` as `sub(srl(add(a, 2^63), n), srl(2^63, n))` instead.
    fn new_sra(&mut self, value: NodeRef, shift: NodeRef) -> NodeRef {
        let const_node = self.new_const(1 << 63);
        let add_node = self.new_add(value, const_node.clone());
        let srl1_node = self.new_srl(add_node, shift.clone());
        let srl2_node = self.new_srl(const_node, shift);
        self.new_sub(srl1_node, srl2_node)
    }

    fn new_state(&mut self, init: Option<NodeRef>, name: String, sort: NodeType) -> NodeRef {
        let nid_increase = u64::from(init.is_some());
        let state_node = self.add_node(Node::State {
            nid: self.current_nid,
            sort,
            init,
            name: Some(name),
        });
        self.current_nid += nid_increase;
        state_node
    }

    fn new_next(&mut self, state: NodeRef, next: NodeRef, sort: NodeType) -> NodeRef {
        let next_node = self.add_node(Node::Next {
            nid: self.current_nid,
            sort,
            state,
            next,
        });
        self.sequentials.push(next_node.clone());
        next_node
    }

    fn new_input(&mut self, name: String, sort: NodeType) -> NodeRef {
        let input_node = self.add_node(Node::Input {
            nid: self.current_nid,
            sort: sort.clone(),
            name,
        });
        if sort == NodeType::Word {
            return input_node;
        }
        self.add_node(Node::Ext {
            nid: self.current_nid,
            from: sort,
            value: input_node,
        })
    }

    fn new_bad(&mut self, cond: NodeRef, name: &str) -> NodeRef {
        let bad_node = self.add_node(Node::Bad {
            nid: self.current_nid,
            cond,
            name: Some(name.to_string()),
        });
        self.bad_states.push(bad_node.clone());
        bad_node
    }

    fn new_comment(&mut self, s: String) {
        let node = Rc::new(RefCell::new(Node::Comment(s)));
        self.lines.push(node);
    }

    fn go_to_instruction(
        &mut self,
        from_instruction: FromInstruction,
        from_address: u64,
        to_address: u64,
        condition: Option<NodeRef>,
    ) {
        self.control_in
            .entry(to_address)
            .or_insert_with(|| Vec::with_capacity(1))
            .push(InEdge {
                from_instruction,
                from_address,
                condition,
            });
    }

    fn go_to_anywhere(&mut self, from_address: u64, dispatch_register: Register) {
        self.dynamic[dispatch_register as usize - 1].push(DynDispatch {
            dispatch_address: from_address,
        });
    }

    fn model_unimplemented(&mut self, inst: Instruction) {
        let bad_name = format!("unimplemented-pc-{:x} ; {:?}", self.pc, inst);
        self.new_bad(self.pc_flag(), &bad_name);
    }

    fn model_addi(&mut self, itype: IType) {
        if itype.rd() == Register::Zero {
            return;
        };
        let imm = itype.imm() as u64;
        let result_node = if imm == 0 {
            self.reg_node(itype.rs1())
        } else if itype.rs1() == Register::Zero {
            self.new_const(imm)
        } else {
            let imm_node = self.new_const(imm);
            self.new_add(self.reg_node(itype.rs1()), imm_node)
        };
        self.reg_flow_ite(itype.rd(), result_node);
    }

    fn model_addiw(&mut self, itype: IType) {
        let imm_node = self.new_const(itype.imm() as u64);
        let add_node = self.new_add(self.reg_node(itype.rs1()), imm_node);
        let thirtytwo = self.new_const(32); // for (val << 32) >>s 32
        let sll_node = self.new_sll(add_node, thirtytwo.clone());
        let sra_node = self.new_sra(sll_node, thirtytwo);
        self.reg_flow_ite(itype.rd(), sra_node);
    }

    fn model_xori(&mut self, itype: IType) {
        let imm_node = self.new_const(itype.imm() as u64);
        let xor_node = self.new_xor(self.reg_node(itype.rs1()), imm_node);
        self.reg_flow_ite(itype.rd(), xor_node);
    }

    fn model_ori(&mut self, itype: IType) {
        let imm_node = self.new_const(itype.imm() as u64);
        let or_node = self.new_or(self.reg_node(itype.rs1()), imm_node);
        self.reg_flow_ite(itype.rd(), or_node);
    }

    fn model_andi(&mut self, itype: IType) {
        let imm_node = self.new_const(itype.imm() as u64);
        let and_node = self.new_and_word(self.reg_node(itype.rs1()), imm_node);
        self.reg_flow_ite(itype.rd(), and_node);
    }

    fn model_slli(&mut self, itype: IType) {
        assert!(itype.imm() < 64, "immediate within bounds");
        let imm_node = self.new_const(itype.imm() as u64);
        let sll_node = self.new_sll(self.reg_node(itype.rs1()), imm_node);
        self.reg_flow_ite(itype.rd(), sll_node);
    }

    // We represent `slliw(a, n)` as `(a << (n + 32)) >>s 32` instead.
    fn model_slliw(&mut self, itype: IType) {
        assert!(itype.imm() < 32, "immediate within bounds");
        let imm_node = self.new_const(itype.imm() as u64 + 32);
        let thirtytwo = self.new_const(32); // for val >>s 32
        let sll_node = self.new_sll(self.reg_node(itype.rs1()), imm_node);
        let sra_node = self.new_sra(sll_node, thirtytwo);
        self.reg_flow_ite(itype.rd(), sra_node);
    }

    fn model_sllw(&mut self, rtype: RType) {
        let thirtytwo = self.new_const(32);

        // Only the low 4 bits of rs2 are considered for the shift amount.
        let mask_node = self.new_const(0x1f); // TODO: Make this a global constant.
        let amount_node = self.new_and_word(self.reg_node(rtype.rs2()), mask_node);

        let amount_node_sum = self.new_add(amount_node, thirtytwo.clone());

        // shift left by n[0:4] + 32
        let sll_node = self.new_sll(self.reg_node(rtype.rs1()), amount_node_sum);

        // shift right by 32
        let sra_node = self.new_sra(sll_node, thirtytwo);
        self.reg_flow_ite(rtype.rd(), sra_node);
    }

    fn model_srli(&mut self, itype: IType) {
        assert!(itype.imm() < 64, "immediate within bounds");
        let imm_node = self.new_const(itype.imm() as u64);
        let srl_node = self.new_srl(self.reg_node(itype.rs1()), imm_node);
        self.reg_flow_ite(itype.rd(), srl_node);
    }

    // We represent `srliw(a, n)` as `(a << 32) >>u (n + 32)` instead.
    fn model_srliw(&mut self, itype: IType) {
        assert!(itype.imm() < 32, "immediate within bounds");
        assert!(itype.imm() != 0, "modeling broken for zero-shift");
        let imm_node = self.new_const(itype.imm() as u64 + 32);
        let thirtytwo = self.new_const(32); // for val << 32
        let sll_node = self.new_sll(self.reg_node(itype.rs1()), thirtytwo);
        let srl_node = self.new_srl(sll_node, imm_node);
        self.reg_flow_ite(itype.rd(), srl_node);
    }

    fn model_srai(&mut self, itype: IType) {
        let imm_truncated = (itype.imm() & 0x3f) as u32;
        assert!(imm_truncated < 64, "immediate within bounds");
        let imm_node = self.new_const(imm_truncated as u64);
        let sra_node = self.new_sra(self.reg_node(itype.rs1()), imm_node);
        self.reg_flow_ite(itype.rd(), sra_node);
    }

    // We represent `sraiw(a, n)` as `(a << 32) >>s (n + 32)` instead.
    fn model_sraiw(&mut self, itype: IType) {
        let imm_truncated = (itype.imm() & 0x3f) as u32;
        assert!(imm_truncated < 32, "immediate within bounds");
        let imm_node = self.new_const(imm_truncated as u64 + 32);
        let thirtytwo = self.new_const(32); // for val << 32
        let sll_node = self.new_sll(self.reg_node(itype.rs1()), thirtytwo);
        let sra_node = self.new_sra(sll_node, imm_node);
        self.reg_flow_ite(itype.rd(), sra_node);
    }

    fn model_lui(&mut self, utype: UType) {
        let imm_shifted = ((utype.imm() as i32) << 12) as u64;
        let const_node = self.new_const(imm_shifted);
        self.reg_flow_ite(utype.rd(), const_node);
    }

    fn model_auipc(&mut self, utype: UType) {
        let imm_shifted = ((utype.imm() as i32) << 12) as u64;
        let const_node = self.new_const(imm_shifted + self.pc);
        self.reg_flow_ite(utype.rd(), const_node);
    }

    fn model_address(&mut self, reg: Register, imm: u64) -> NodeRef {
        if imm == 0 {
            self.reg_node(reg)
        } else {
            let imm_node = self.new_const(imm);
            self.new_add(self.reg_node(reg), imm_node)
        }
    }

    // We represent n-bit load operations `load(n, adr, sig)` as:
    //   word := adr & ~WORD_SIZE_MASK
    //   prev := load(word)
    //   left := prev << (64 - n - 8 * (adr & WORD_SIZE_MASK))
    //   return left >>s (64 - n)       ||| if (sig == true)
    //          left >>u (64 - n)       ||| if (sig == false)
    //
    // Note that the above approach even works for unaligned loads as
    // long as the load does not cross word-boundaries.
    fn model_l(&mut self, bits: u32, address: NodeRef, signed: bool) -> NodeRef {
        assert!(bits > 0 && bits < 64, "bit-width within range");
        let address_mask_node = self.new_const(!WORD_SIZE_MASK);
        let address_word_node = self.new_and_word(address.clone(), address_mask_node);
        self.access_flow = self.new_ite(
            self.pc_flag(),
            address_word_node.clone(),
            self.access_flow.clone(),
            NodeType::Word,
        );
        let read_node = self.new_read(address_word_node);
        let eight_node = self.new_const(BITS_PER_BYTE);
        let address_mask_node = self.new_const(WORD_SIZE_MASK);
        let address_offset_node = self.new_and_word(address, address_mask_node);
        let shift_amount_node = self.new_mul(eight_node, address_offset_node);
        let shift_const_node = self.new_const(64 - bits as u64);
        let left_shift_amount = self.new_sub(shift_const_node.clone(), shift_amount_node);
        let left_shift_node = self.new_sll(read_node, left_shift_amount);
        if signed {
            self.new_sra(left_shift_node, shift_const_node)
        } else {
            self.new_srl(left_shift_node, shift_const_node)
        }
    }

    fn model_lb(&mut self, itype: IType) {
        let address_node = self.model_address(itype.rs1(), itype.imm() as u64);
        let load_node = self.model_l(8, address_node, true);
        self.reg_flow_ite(itype.rd(), load_node);
    }

    fn model_lbu(&mut self, itype: IType) {
        let address_node = self.model_address(itype.rs1(), itype.imm() as u64);
        let load_node = self.model_l(8, address_node, false);
        self.reg_flow_ite(itype.rd(), load_node);
    }

    fn model_lh(&mut self, itype: IType) {
        let address_node = self.model_address(itype.rs1(), itype.imm() as u64);
        let load_node = self.model_l(16, address_node, true);
        self.reg_flow_ite(itype.rd(), load_node);
    }

    fn model_lhu(&mut self, itype: IType) {
        let address_node = self.model_address(itype.rs1(), itype.imm() as u64);
        let load_node = self.model_l(16, address_node, false);
        self.reg_flow_ite(itype.rd(), load_node);
    }

    fn model_lw(&mut self, itype: IType) {
        let address_node = self.model_address(itype.rs1(), itype.imm() as u64);
        let load_node = self.model_l(32, address_node, true);
        self.reg_flow_ite(itype.rd(), load_node);
    }

    fn model_ld(&mut self, itype: IType) {
        let address_node = self.model_address(itype.rs1(), itype.imm() as u64);
        self.access_flow = self.new_ite(
            self.pc_flag(),
            address_node.clone(),
            self.access_flow.clone(),
            NodeType::Word,
        );
        let read_node = self.new_read(address_node);
        self.reg_flow_ite(itype.rd(), read_node);
    }

    // We represent n-bit store operations `store(n, adr, val)` as:
    //   word := adr & ~WORD_SIZE_MASK
    //   mask := ONES(n) << 8 * (adr & WORD_SIZE_MASK)
    //   valu := val << 8 * (adr & WORD_SIZE_MASK)
    //   prev := load(word)
    //   updt := (valu & mask) | (prev & ~mask)
    //   return store(word, updt)
    //
    // Note that the above approach even works for unaligned stores as
    // long as the store does not cross word-boundaries.
    fn model_s(&mut self, bits: u32, address: NodeRef, value: NodeRef) {
        assert!(bits > 0 && bits < 64, "bit-width within range");
        let address_mask_node = self.new_const(!WORD_SIZE_MASK);
        let address_word_node = self.new_and_word(address.clone(), address_mask_node);
        self.access_flow = self.new_ite(
            self.pc_flag(),
            address_word_node.clone(),
            self.access_flow.clone(),
            NodeType::Word,
        );
        let read_node = self.new_read(address_word_node.clone());
        let ones_node = self.new_const((1 << bits) - 1);
        let eight_node = self.new_const(BITS_PER_BYTE);
        let address_mask_node = self.new_const(WORD_SIZE_MASK);
        let address_offset_node = self.new_and_word(address, address_mask_node);
        let shift_amount_node = self.new_mul(eight_node, address_offset_node);
        let mask_node = self.new_sll(ones_node, shift_amount_node.clone());
        let mask_not_node = self.new_not_word(mask_node.clone());
        let value_node = self.new_sll(value, shift_amount_node);
        let and1_node = self.new_and_word(value_node, mask_node);
        let and2_node = self.new_and_word(read_node, mask_not_node);
        let or_node = self.new_or(and1_node, and2_node);
        let write_node = self.new_write(address_word_node, or_node);
        let ite_node = self.new_ite(
            self.pc_flag(),
            write_node,
            self.memory_flow.clone(),
            NodeType::Memory,
        );
        self.memory_flow = ite_node;
    }

    fn model_sb(&mut self, stype: SType) {
        let address_node = self.model_address(stype.rs1(), stype.imm() as u64);
        self.model_s(8, address_node, self.reg_node(stype.rs2()))
    }

    fn model_sh(&mut self, stype: SType) {
        let address_node = self.model_address(stype.rs1(), stype.imm() as u64);
        self.model_s(16, address_node, self.reg_node(stype.rs2()))
    }

    fn model_sw(&mut self, stype: SType) {
        let address_node = self.model_address(stype.rs1(), stype.imm() as u64);
        self.model_s(32, address_node, self.reg_node(stype.rs2()))
    }

    fn model_sd(&mut self, stype: SType) {
        let address_node = self.model_address(stype.rs1(), stype.imm() as u64);
        self.access_flow = self.new_ite(
            self.pc_flag(),
            address_node.clone(),
            self.access_flow.clone(),
            NodeType::Word,
        );
        let write_node = self.new_write(address_node, self.reg_node(stype.rs2()));
        let ite_node = self.new_ite(
            self.pc_flag(),
            write_node,
            self.memory_flow.clone(),
            NodeType::Memory,
        );
        self.memory_flow = ite_node;
    }

    fn model_add(&mut self, rtype: RType) {
        let add_node = self.new_add(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), add_node);
    }

    fn model_addw(&mut self, rtype: RType) {
        let add_node = self.new_add(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        let thirtytwo = self.new_const(32);
        let sll_node = self.new_sll(add_node, thirtytwo.clone());
        let sra_node = self.new_sra(sll_node, thirtytwo);
        self.reg_flow_ite(rtype.rd(), sra_node);
    }

    fn model_sub(&mut self, rtype: RType) {
        let sub_node = self.new_sub(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), sub_node);
    }

    fn model_subw(&mut self, rtype: RType) {
        let sub_node = self.new_sub(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        let thirtytwo = self.new_const(32);
        let sll_node = self.new_sll(sub_node, thirtytwo.clone());
        let sra_node = self.new_sra(sll_node, thirtytwo);
        self.reg_flow_ite(rtype.rd(), sra_node);
    }

    fn model_or(&mut self, rtype: RType) {
        let or_node = self.new_or(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), or_node);
    }

    fn model_and(&mut self, rtype: RType) {
        let and_node = self.new_and_word(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), and_node);
    }

    fn model_sll(&mut self, rtype: RType) {
        // Only the low 6 bits of rs2 are considered for the shift amount.
        let mask_node = self.new_const(0x3f); // TODO: Make this a global constant.
        let amount_node = self.new_and_word(self.reg_node(rtype.rs2()), mask_node);
        let sll_node = self.new_sll(self.reg_node(rtype.rs1()), amount_node);
        self.reg_flow_ite(rtype.rd(), sll_node);
    }

    fn model_srl(&mut self, rtype: RType) {
        // Only the low 6 bits of rs2 are considered for the shift amount.
        let mask_node = self.new_const(0x3f); // TODO: Make this a global constant.
        let amount_node = self.new_and_word(self.reg_node(rtype.rs2()), mask_node);
        let srl_node = self.new_srl(self.reg_node(rtype.rs1()), amount_node);
        self.reg_flow_ite(rtype.rd(), srl_node);
    }

    fn model_sra(&mut self, rtype: RType) {
        // Only the low 6 bits of rs2 are considered for the shift amount.
        let mask_node = self.new_const(0x3f); // TODO: Make this a global constant.
        let amount_node = self.new_and_word(self.reg_node(rtype.rs2()), mask_node);
        let sra_node = self.new_sra(self.reg_node(rtype.rs1()), amount_node);
        self.reg_flow_ite(rtype.rd(), sra_node);
    }

    fn model_mul(&mut self, rtype: RType) {
        let mul_node = self.new_mul(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), mul_node);
    }

    fn model_mulw(&mut self, rtype: RType) {
        let thirtytwo = self.new_const(32);
        // sign extend each operand
        let mut left_sext = self.new_sll(self.reg_node(rtype.rs1()), thirtytwo.clone());
        left_sext = self.new_sra(left_sext, thirtytwo.clone());

        let mut right_sext = self.new_sll(self.reg_node(rtype.rs2()), thirtytwo.clone());
        right_sext = self.new_sra(right_sext, thirtytwo.clone());

        let mul_node = self.new_mul(left_sext, right_sext);

        let mut sext_mul_node = self.new_sll(mul_node, thirtytwo.clone());
        sext_mul_node = self.new_sra(sext_mul_node, thirtytwo);

        self.reg_flow_ite(rtype.rd(), sext_mul_node);
    }

    fn model_divu(&mut self, rtype: RType) {
        self.division_flow = self.new_ite(
            self.pc_flag(),
            self.reg_node(rtype.rs2()),
            self.division_flow.clone(),
            NodeType::Word,
        );
        let div_node = self.new_divu(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), div_node);
    }

    fn model_div(&mut self, rtype: RType) {
        self.division_flow = self.new_ite(
            self.pc_flag(),
            self.reg_node(rtype.rs2()),
            self.division_flow.clone(),
            NodeType::Word,
        );
        let div_node = self.new_div(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), div_node);
    }

    fn model_divw(&mut self, rtype: RType) {
        let thirtytwo = self.new_const(32);
        // sign extend each operand
        let mut left_sext = self.new_sll(self.reg_node(rtype.rs1()), thirtytwo.clone());
        left_sext = self.new_sra(left_sext, thirtytwo.clone());

        let mut right_sext = self.new_sll(self.reg_node(rtype.rs2()), thirtytwo.clone());
        right_sext = self.new_sra(right_sext, thirtytwo);

        // perform 64-bit signed division
        let divw_node = self.new_div(left_sext, right_sext);

        self.reg_flow_ite(rtype.rd(), divw_node);
    }

    fn model_remu(&mut self, rtype: RType) {
        self.remainder_flow = self.new_ite(
            self.pc_flag(),
            self.reg_node(rtype.rs2()),
            self.remainder_flow.clone(),
            NodeType::Word,
        );
        let rem_node = self.new_rem(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        self.reg_flow_ite(rtype.rd(), rem_node);
    }

    fn model_sltu(&mut self, rtype: RType) {
        let ult_node = self.new_ult(self.reg_node(rtype.rs1()), self.reg_node(rtype.rs2()));
        let ext_node = self.add_node(Node::Ext {
            nid: self.current_nid,
            from: NodeType::Bit,
            value: ult_node,
        });
        self.reg_flow_ite(rtype.rd(), ext_node);
    }

    fn model_sltiu(&mut self, itype: IType) {
        let imm = itype.imm() as u64;
        let imm_node = self.new_const(imm);

        let ult_node = self.new_ult(self.reg_node(itype.rs1()), imm_node);
        let ext_node = self.add_node(Node::Ext {
            nid: self.current_nid,
            from: NodeType::Bit,
            value: ult_node,
        });
        self.reg_flow_ite(itype.rd(), ext_node);
    }

    fn model_branch<F>(
        &mut self,
        btype: BType,
        out_true: &mut Option<NodeRef>,
        out_false: &mut Option<NodeRef>,
        f_new_cond: F,
    ) where
        F: FnOnce(&mut Self, NodeRef, NodeRef) -> NodeRef,
    {
        let cond_true = f_new_cond(self, self.reg_node(btype.rs1()), self.reg_node(btype.rs2()));
        let cond_false = self.new_not_bit(cond_true.clone());
        out_true.replace(cond_true);
        out_false.replace(cond_false);
    }

    fn model_beq(&mut self, btype: BType, t: &mut Option<NodeRef>, f: &mut Option<NodeRef>) {
        self.model_branch(btype, t, f, Self::new_eq)
    }

    fn model_bne(&mut self, btype: BType, t: &mut Option<NodeRef>, f: &mut Option<NodeRef>) {
        self.model_branch(btype, t, f, Self::new_neq)
    }

    fn model_blt(&mut self, btype: BType, t: &mut Option<NodeRef>, f: &mut Option<NodeRef>) {
        self.model_branch(btype, t, f, Self::new_slt)
    }

    fn model_bge(&mut self, btype: BType, t: &mut Option<NodeRef>, f: &mut Option<NodeRef>) {
        self.model_branch(btype, t, f, Self::new_sgte)
    }

    fn model_bltu(&mut self, btype: BType, t: &mut Option<NodeRef>, f: &mut Option<NodeRef>) {
        self.model_branch(btype, t, f, Self::new_ult)
    }

    fn model_bgeu(&mut self, btype: BType, t: &mut Option<NodeRef>, f: &mut Option<NodeRef>) {
        self.model_branch(btype, t, f, Self::new_ugte)
    }

    fn model_jal(&mut self, jtype: JType) {
        if jtype.rd() == Register::Zero {
            return;
        };
        let link_node = self.new_const(self.pc_add(INSTRUCTION_SIZE));
        self.reg_flow_ite(jtype.rd(), link_node);
    }

    fn model_jalr(&mut self, itype: IType) {
        if itype.rd() == Register::Zero {
            return;
        };
        let link_node = self.new_const(self.pc_add(INSTRUCTION_SIZE));
        self.reg_flow_ite(itype.rd(), link_node);
    }

    fn model_ecall(&mut self) {
        let ite_node = self.new_ite(
            self.pc_flag(),
            self.one_bit.clone(),
            self.ecall_flow.clone(),
            NodeType::Bit,
        );
        self.ecall_flow = ite_node;
    }

    fn translate_to_model(&mut self, inst: Instruction) {
        let mut branch_true = None;
        let mut branch_false = None;

        match inst {
            Instruction::Lui(utype) => self.model_lui(utype),
            Instruction::Auipc(utype) => self.model_auipc(utype),
            Instruction::Lb(itype) => self.model_lb(itype),
            Instruction::Lh(itype) => self.model_lh(itype),
            Instruction::Lw(itype) => self.model_lw(itype),
            Instruction::Ld(itype) => self.model_ld(itype),
            Instruction::Lbu(itype) => self.model_lbu(itype),
            Instruction::Lhu(itype) => self.model_lhu(itype),
            Instruction::Sb(stype) => self.model_sb(stype),
            Instruction::Sh(stype) => self.model_sh(stype),
            Instruction::Sw(stype) => self.model_sw(stype),
            Instruction::Sd(stype) => self.model_sd(stype),
            Instruction::Addi(itype) => self.model_addi(itype),
            Instruction::Sltiu(itype) => self.model_sltiu(itype),
            Instruction::Xori(itype) => self.model_xori(itype),
            Instruction::Ori(itype) => self.model_ori(itype),
            Instruction::Andi(itype) => self.model_andi(itype),
            Instruction::Slli(itype) => self.model_slli(itype),
            Instruction::Srli(itype) => self.model_srli(itype),
            Instruction::Srai(itype) => self.model_srai(itype),
            Instruction::Addiw(itype) => self.model_addiw(itype),
            Instruction::Slliw(itype) => self.model_slliw(itype),
            Instruction::Srliw(itype) => self.model_srliw(itype),
            Instruction::Sraiw(itype) => self.model_sraiw(itype),
            Instruction::Add(rtype) => self.model_add(rtype),
            Instruction::Sub(rtype) => self.model_sub(rtype),
            Instruction::Sll(rtype) => self.model_sll(rtype),
            Instruction::Sltu(rtype) => self.model_sltu(rtype),
            Instruction::Srl(rtype) => self.model_srl(rtype),
            Instruction::Sra(rtype) => self.model_sra(rtype),
            Instruction::Or(rtype) => self.model_or(rtype),
            Instruction::And(rtype) => self.model_and(rtype),
            Instruction::Mul(rtype) => self.model_mul(rtype),
            Instruction::Div(rtype) => self.model_div(rtype),
            Instruction::Divu(rtype) => self.model_divu(rtype),
            Instruction::Remu(rtype) => self.model_remu(rtype),
            Instruction::Addw(rtype) => self.model_addw(rtype),
            Instruction::Divw(rtype) => self.model_divw(rtype),
            Instruction::Subw(rtype) => self.model_subw(rtype),
            Instruction::Sllw(rtype) => self.model_sllw(rtype),
            Instruction::Mulw(rtype) => self.model_mulw(rtype),
            Instruction::Beq(btype) => self.model_beq(btype, &mut branch_true, &mut branch_false),
            Instruction::Bne(btype) => self.model_bne(btype, &mut branch_true, &mut branch_false),
            Instruction::Blt(btype) => self.model_blt(btype, &mut branch_true, &mut branch_false),
            Instruction::Bge(btype) => self.model_bge(btype, &mut branch_true, &mut branch_false),
            Instruction::Bltu(btype) => self.model_bltu(btype, &mut branch_true, &mut branch_false),
            Instruction::Bgeu(btype) => self.model_bgeu(btype, &mut branch_true, &mut branch_false),
            Instruction::Jal(jtype) => self.model_jal(jtype),
            Instruction::Jalr(itype) => self.model_jalr(itype),
            Instruction::Ecall(_) => self.model_ecall(),
            _ => todo!("{:?}", inst),
        }

        match inst {
            Instruction::Lui(_)
            | Instruction::Auipc(_)
            | Instruction::Lb(_)
            | Instruction::Lh(_)
            | Instruction::Lw(_)
            | Instruction::Ld(_)
            | Instruction::Lbu(_)
            | Instruction::Lhu(_)
            | Instruction::Lwu(_)
            | Instruction::Sb(_)
            | Instruction::Sh(_)
            | Instruction::Sw(_)
            | Instruction::Sd(_)
            | Instruction::Addi(_)
            | Instruction::Sltiu(_)
            | Instruction::Xori(_)
            | Instruction::Ori(_)
            | Instruction::Andi(_)
            | Instruction::Slli(_)
            | Instruction::Srli(_)
            | Instruction::Srai(_)
            | Instruction::Addiw(_)
            | Instruction::Slliw(_)
            | Instruction::Srliw(_)
            | Instruction::Sraiw(_)
            | Instruction::Add(_)
            | Instruction::Sub(_)
            | Instruction::Sll(_)
            | Instruction::Sltu(_)
            | Instruction::Srl(_)
            | Instruction::Sra(_)
            | Instruction::Or(_)
            | Instruction::And(_)
            | Instruction::Mul(_)
            | Instruction::Div(_)
            | Instruction::Divu(_)
            | Instruction::Remu(_)
            | Instruction::Addw(_)
            | Instruction::Subw(_)
            | Instruction::Sllw(_)
            | Instruction::Mulw(_)
            | Instruction::Divw(_) => {
                self.go_to_instruction(
                    FromInstruction::Regular,
                    self.pc,
                    self.pc_add(INSTRUCTION_SIZE),
                    None,
                );
            }
            Instruction::Beq(btype)
            | Instruction::Bne(btype)
            | Instruction::Blt(btype)
            | Instruction::Bge(btype)
            | Instruction::Bltu(btype)
            | Instruction::Bgeu(btype) => {
                assert!(branch_true.is_some(), "was set");
                assert!(branch_false.is_some(), "was set");
                self.go_to_instruction(
                    FromInstruction::Branch,
                    self.pc,
                    self.pc_add(btype.imm() as u64),
                    branch_true,
                );
                self.go_to_instruction(
                    FromInstruction::Branch,
                    self.pc,
                    self.pc_add(INSTRUCTION_SIZE),
                    branch_false,
                );
            }
            Instruction::Jal(jtype) => {
                self.go_to_instruction(
                    FromInstruction::Regular,
                    self.pc,
                    self.pc_add(jtype.imm() as u64),
                    None,
                );
            }
            Instruction::Jalr(itype) => {
                if itype.rs1() == Register::Zero {
                    // TODO: Find a proper modeling for this.
                    warn!("Detected JALR dispatch on zero: {:#x}: {:?}", self.pc, inst);
                    self.model_unimplemented(inst);
                    return;
                }
                assert_eq!(itype.imm(), 0, "dispatch with offset");
                self.go_to_anywhere(self.pc, itype.rs1());
            }
            Instruction::Ecall(_) => {
                self.go_to_instruction(
                    FromInstruction::SystemCall,
                    self.pc,
                    self.pc_add(INSTRUCTION_SIZE),
                    None,
                );
            }
            _ => todo!("{:?}", inst),
        }
    }

    fn control_flow_from_regular(&mut self, edge: &InEdge, flow: NodeRef) -> NodeRef {
        self.control_flow_from_any(self.pc_flags[&edge.from_address].clone(), flow)
    }

    fn control_flow_from_branch(&mut self, edge: &InEdge, flow: NodeRef) -> NodeRef {
        let and_node = self.new_and_bit(
            self.pc_flags[&edge.from_address].clone(),
            edge.condition.as_ref().expect("must exist").clone(),
        );
        self.control_flow_from_any(and_node, flow)
    }

    fn control_flow_from_ecall(&mut self, edge: &InEdge, flow: NodeRef) -> NodeRef {
        let state_node = self.new_state(
            Some(self.zero_bit.clone()),
            format!("kernel-mode-pc-flag-{}", edge.from_address),
            NodeType::Bit,
        );
        let ite_node = self.new_ite(
            state_node.clone(),
            self.kernel_mode.clone(),
            self.pc_flags[&edge.from_address].clone(),
            NodeType::Bit,
        );
        self.new_next(state_node.clone(), ite_node, NodeType::Bit);
        let and_node = self.new_and_bit(state_node, self.kernel_not.clone());
        self.control_flow_from_any(and_node, flow)
    }

    fn control_flow_from_jalr(&mut self, reg: Register, pc: NodeRef, flow: NodeRef) -> NodeRef {
        let eq_node = self.new_eq(self.reg_node(reg), pc);
        let and_node = self.new_and_bit(self.dynamic_flag(reg), eq_node);
        self.control_flow_from_any(and_node, flow)
    }

    fn control_flow_from_any(&mut self, activate: NodeRef, flow: NodeRef) -> NodeRef {
        if Rc::ptr_eq(&flow, &self.zero_bit) {
            return activate;
        }
        self.new_ite(activate, self.one_bit.clone(), flow, NodeType::Bit)
    }

    fn generate_model(&mut self, program: &Program, argv: &[String]) -> Result<()> {
        let data_start = program.data.address;
        let data_end = program.data.address + program.data.content.len() as u64;
        self.data_range = data_start..data_end;
        let heap_start = next_multiple_of(data_end, PAGE_SIZE);
        let heap_end = heap_start + self.max_heap_size;
        self.heap_range = heap_start..heap_end;
        let stack_start = self.memory_size - self.max_stack_size;
        let stack_end = self.memory_size;
        self.stack_range = stack_start..stack_end;

        debug!("argc: {}, argv: {:?}", argv.len(), argv);
        let initial_stack = prepare_unix_stack(argv, stack_end);
        let initial_stack_size = initial_stack.len() * size_of::<u64>();
        let initial_sp_value = stack_end - initial_stack_size as u64;
        assert!(initial_sp_value >= stack_start, "initial stack fits");

        self.new_comment("common constants".to_string());
        self.zero_bit = self.add_node(Node::Const {
            nid: 20,
            sort: NodeType::Bit,
            imm: 0,
        });
        self.one_bit = self.add_node(Node::Const {
            nid: 21,
            sort: NodeType::Bit,
            imm: 1,
        });
        self.zero_word = self.add_node(Node::Const {
            nid: 30,
            sort: NodeType::Word,
            imm: 0,
        });
        self.division_flow = self.add_node(Node::Const {
            nid: 31,
            sort: NodeType::Word,
            imm: 1,
        });
        self.remainder_flow = self.division_flow.clone();
        self.access_flow = self.add_node(Node::Const {
            nid: 40,
            sort: NodeType::Word,
            imm: self.data_range.start,
        });
        self.ecall_flow = self.zero_bit.clone();

        self.new_comment("kernel-mode flag".to_string());
        self.current_nid = 60;
        self.kernel_mode = self.new_state(
            Some(self.zero_bit.clone()),
            "kernel-mode".to_string(),
            NodeType::Bit,
        );
        self.kernel_not = self.new_not_bit(self.kernel_mode.clone());

        self.new_comment("32 64-bit general-purpose registers".to_string());
        self.current_nid = 200;
        let zero_register = self.new_const(0);
        let sp_value = self.new_const(initial_sp_value);
        self.register_nodes.push(zero_register);
        for r in 1..NUMBER_OF_REGISTERS {
            let reg = Register::from(r as u32);
            self.current_nid = 200 + 2 * r as u64;
            let initial_value = match reg {
                Register::Sp => sp_value.clone(),
                _ => self.zero_word.clone(),
            };
            let register_node =
                self.new_state(Some(initial_value), format!("{:?}", reg), NodeType::Word);
            self.register_nodes.push(register_node.clone());
            self.register_flow.push(register_node);
        }
        assert_eq!(self.register_nodes.len(), NUMBER_OF_REGISTERS);
        assert_eq!(self.register_flow.len(), NUMBER_OF_REGISTERS - 1);

        self.new_comment("32 dynamic dispatch indicators as Boolean flags".to_string());
        for r in 1..NUMBER_OF_REGISTERS {
            let reg = Register::from(r as u32);
            self.current_nid = 300 + 2 * r as u64;
            let flag_node = self.new_state(
                Some(self.zero_bit.clone()),
                format!("dynamic-dispatch-on-{:?}", reg),
                NodeType::Bit,
            );
            self.dynamic_flags.push(flag_node);
            self.dynamic.push(vec![]);
        }
        assert_eq!(self.dynamic_flags.len(), NUMBER_OF_REGISTERS - 1);
        assert_eq!(self.dynamic.len(), NUMBER_OF_REGISTERS - 1);

        self.new_comment("64-bit program counter encoded in Boolean flags".to_string());
        self.pc = program.instruction_range.start;
        for n in program.instruction_range.clone().step_by(size_of::<u32>()) {
            self.current_nid = 10000000 + self.pc * 100;
            let initial_value = if n == program.instruction_range.start {
                self.one_bit.clone()
            } else {
                self.zero_bit.clone()
            };
            let flag_node = self.new_state(
                Some(initial_value),
                format!("pc={:#x}", self.pc),
                NodeType::Bit,
            );
            self.pc_flags.insert(self.pc, flag_node);
            self.pc = self.pc_add(INSTRUCTION_SIZE);
        }

        self.new_comment("64-bit virtual memory".to_string());
        self.current_nid = 20000000;
        self.memory_node = self.new_state(None, "memory-dump".to_string(), NodeType::Memory);
        let dump_start = data_start & !(size_of::<u64>() as u64 - 1);
        let dump_end = next_multiple_of(data_end, size_of::<u64>() as u64);
        let mut dump_buffer = Vec::from(&program.data.content[..]);
        if dump_start != data_start {
            let padding = (data_start - dump_start) as usize;
            debug!("Aligning data start: {:#010x}+{}", dump_start, padding);
            dump_buffer = [vec![0; padding], dump_buffer].concat();
        }
        if dump_end != data_end {
            let padding = (dump_end - data_end) as usize;
            debug!("Aligning data end: {:#010x}-{}", dump_end, padding);
            dump_buffer.extend(vec![0; padding]);
        }
        assert!(dump_buffer.len() % size_of::<u64>() == 0, "has been padded");
        fn write_value_to_memory(this: &mut ModelBuilder, val: u64, adr: u64) {
            let address = this.new_const(adr);
            let value = if val == 0 {
                this.zero_word.clone()
            } else {
                this.new_const(val)
            };
            this.memory_node = this.new_write(address, value);
        }
        dump_buffer
            .chunks(size_of::<u64>())
            .map(LittleEndian::read_u64)
            .zip((dump_start..dump_end).step_by(size_of::<u64>()))
            .for_each(|(val, adr)| write_value_to_memory(self, val, adr));
        initial_stack
            .into_iter()
            .rev()
            .zip((initial_sp_value..stack_end).step_by(size_of::<u64>()))
            .for_each(|(val, adr)| write_value_to_memory(self, val, adr));
        self.memory_node = self.new_state(
            Some(self.memory_node.clone()),
            "virtual-memory".to_string(),
            NodeType::Memory,
        );
        self.memory_flow = self.memory_node.clone();

        self.new_comment("data flow".to_string());
        self.pc = program.instruction_range.start;
        program
            .instructions()
            .chunks(size_of::<u32>())
            .map(LittleEndian::read_u32)
            .try_for_each(|raw| {
                decode(raw).map(|inst| {
                    self.current_nid = 30000000 + self.pc * 100;
                    self.translate_to_model(inst);
                    self.pc = self.pc_add(INSTRUCTION_SIZE);
                })
            })
            .context("Failed to decode instructions of program")?;

        self.new_comment("syscalls".to_string());
        self.current_nid = 40000000;
        let mut kernel_flow = self.kernel_mode.clone();
        let num_openat = self.new_const(SyscallId::Openat as u64);
        let is_openat = self.new_eq(self.reg_node(Register::A7), num_openat);
        let num_read = self.new_const(SyscallId::Read as u64);
        let is_read = self.new_eq(self.reg_node(Register::A7), num_read);
        let num_write = self.new_const(SyscallId::Write as u64);
        let is_write = self.new_eq(self.reg_node(Register::A7), num_write);
        let num_exit = self.new_const(SyscallId::Exit as u64);
        let is_exit = self.new_eq(self.reg_node(Register::A7), num_exit);
        let num_brk = self.new_const(SyscallId::Brk as u64);
        let is_brk = self.new_eq(self.reg_node(Register::A7), num_brk);

        self.current_nid = 41000000;
        let active_exit = self.new_and_bit(self.ecall_flow.clone(), is_exit.clone());
        kernel_flow = self.new_ite(
            kernel_flow,
            is_exit.clone(),
            active_exit.clone(),
            NodeType::Bit,
        );

        self.current_nid = 42000000;
        let active_read = self.new_and_bit(self.ecall_flow.clone(), is_read.clone());
        kernel_flow = self.new_ite(
            active_read.clone(),
            self.one_bit.clone(),
            kernel_flow,
            NodeType::Bit,
        );
        let read_a0_zero = self.new_ite(
            active_read,
            self.zero_word.clone(),
            self.reg_flow(Register::A0),
            NodeType::Word,
        );
        let read_remaining = self.new_sub(self.reg_node(Register::A2), self.reg_node(Register::A0));
        let read_const_8 = self.new_const(8);
        let read_full_word = self.new_ugte(read_remaining.clone(), read_const_8.clone());
        let read_bytes = self.new_ite(read_full_word, read_const_8, read_remaining, NodeType::Word);
        let read_input1 = self.new_input("1-byte-input".to_string(), NodeType::Input1Byte);
        let read_input2 = self.new_input("2-byte-input".to_string(), NodeType::Input2Byte);
        let read_const_2 = self.new_const(2);
        let read_bytes_eq_2 = self.new_eq(read_bytes.clone(), read_const_2);
        let read_ite_2 = self.new_ite(read_bytes_eq_2, read_input2, read_input1, NodeType::Word);
        let read_input3 = self.new_input("3-byte-input".to_string(), NodeType::Input3Byte);
        let read_const_3 = self.new_const(3);
        let read_bytes_eq_3 = self.new_eq(read_bytes.clone(), read_const_3);
        let read_ite_3 = self.new_ite(read_bytes_eq_3, read_input3, read_ite_2, NodeType::Word);
        let read_input4 = self.new_input("4-byte-input".to_string(), NodeType::Input4Byte);
        let read_const_4 = self.new_const(4);
        let read_bytes_eq_4 = self.new_eq(read_bytes.clone(), read_const_4);
        let read_ite_4 = self.new_ite(read_bytes_eq_4, read_input4, read_ite_3, NodeType::Word);
        let read_input5 = self.new_input("5-byte-input".to_string(), NodeType::Input5Byte);
        let read_const_5 = self.new_const(5);
        let read_bytes_eq_5 = self.new_eq(read_bytes.clone(), read_const_5);
        let read_ite_5 = self.new_ite(read_bytes_eq_5, read_input5, read_ite_4, NodeType::Word);
        let read_input6 = self.new_input("6-byte-input".to_string(), NodeType::Input6Byte);
        let read_const_6 = self.new_const(6);
        let read_bytes_eq_6 = self.new_eq(read_bytes.clone(), read_const_6);
        let read_ite_6 = self.new_ite(read_bytes_eq_6, read_input6, read_ite_5, NodeType::Word);
        let read_input7 = self.new_input("7-byte-input".to_string(), NodeType::Input7Byte);
        let read_const_7 = self.new_const(7);
        let read_bytes_eq_7 = self.new_eq(read_bytes.clone(), read_const_7);
        let read_ite_7 = self.new_ite(read_bytes_eq_7, read_input7, read_ite_6, NodeType::Word);
        let read_input8 = self.new_input("8-byte-input".to_string(), NodeType::Word);
        let read_const_8 = self.new_const(8);
        let read_bytes_eq_8 = self.new_eq(read_bytes.clone(), read_const_8);
        let read_ite_8 = self.new_ite(read_bytes_eq_8, read_input8, read_ite_7, NodeType::Word);
        let read_address = self.new_add(self.reg_node(Register::A1), self.reg_node(Register::A0));
        let read_store = self.new_write(read_address, read_ite_8);
        let read_more = self.new_ult(self.reg_node(Register::A0), self.reg_node(Register::A2));
        let read_more = self.new_and_bit(is_read.clone(), read_more);
        let read_not_done = self.new_and_bit(self.kernel_mode.clone(), read_more);
        let read_not_zero = self.new_ugt(read_bytes.clone(), self.zero_word.clone());
        let read_do_store = self.new_and_bit(read_not_done.clone(), read_not_zero);
        let read_ite_mem = self.new_ite(
            read_do_store,
            read_store,
            self.memory_flow.clone(),
            NodeType::Memory,
        );
        self.memory_flow = read_ite_mem;
        let read_new_a0 = self.new_add(self.reg_node(Register::A0), read_bytes);
        let read_ite_a0 = self.new_ite(
            read_not_done.clone(),
            read_new_a0,
            read_a0_zero,
            NodeType::Word,
        );
        self.reg_flow_update(Register::A0, read_ite_a0);
        kernel_flow = self.new_ite(
            read_not_done,
            self.one_bit.clone(),
            kernel_flow,
            NodeType::Bit,
        );

        self.current_nid = 45000000;
        let active_brk = self.new_and_bit(self.ecall_flow.clone(), is_brk.clone());
        let brk_init = self.new_const(self.heap_range.start);
        let brk_bump = self.new_state(Some(brk_init), "bump-pointer".to_string(), NodeType::Word);
        let brk_lower = self.new_ulte(brk_bump.clone(), self.reg_node(Register::A0));
        let brk_upper = self.new_ult(self.reg_node(Register::A0), self.reg_node(Register::Sp));
        let brk_bound = self.new_and_bit(brk_lower, brk_upper);
        let brk_three_lsb = self.new_const(0b111); // TODO: Make work for 32-bit system
        let brk_mask = self.new_and_word(self.reg_node(Register::A0), brk_three_lsb);
        let brk_aligned = self.new_eq(brk_mask, self.zero_word.clone());
        let brk_valid1 = self.new_and_bit(brk_bound, brk_aligned);
        let brk_valid2 = self.new_and_bit(active_brk.clone(), brk_valid1.clone());
        let brk_bump_ite = self.new_ite(
            brk_valid2,
            self.reg_node(Register::A0),
            brk_bump.clone(),
            NodeType::Word,
        );
        self.new_next(brk_bump.clone(), brk_bump_ite, NodeType::Word);
        let brk_invalid1 = self.new_not_bit(brk_valid1);
        let brk_invalid2 = self.new_and_bit(active_brk, brk_invalid1);
        let brk_a0_ite = self.new_ite(
            brk_invalid2,
            brk_bump.clone(),
            self.reg_flow(Register::A0),
            NodeType::Word,
        );
        self.reg_flow_update(Register::A0, brk_a0_ite);

        self.current_nid = 46000000;
        self.new_next(self.kernel_mode.clone(), kernel_flow, NodeType::Bit);

        self.new_comment("control flow".to_string());
        self.pc = program.instruction_range.start;
        let mut control_flow_update_nodes = HashMap::new();
        let dynamic_dispatches = self.dynamic_dispatches();
        for _n in program.instruction_range.clone().step_by(size_of::<u32>()) {
            self.current_nid = 50000000 + self.pc * 100;
            let mut control_flow = self.zero_bit.clone();
            for in_edge in self.control_in.remove(&self.pc).unwrap_or_default() {
                control_flow = match in_edge.from_instruction {
                    FromInstruction::Branch => {
                        self.control_flow_from_branch(&in_edge, control_flow)
                    }
                    FromInstruction::SystemCall => {
                        self.control_flow_from_ecall(&in_edge, control_flow)
                    }
                    FromInstruction::Regular => {
                        self.control_flow_from_regular(&in_edge, control_flow)
                    }
                }
            }
            let pc = self.new_const(self.pc);
            for reg in dynamic_dispatches.iter().copied() {
                control_flow = self.control_flow_from_jalr(reg, pc.clone(), control_flow);
            }
            control_flow_update_nodes.insert(self.pc, control_flow.clone());
            self.new_next(self.pc_flag(), control_flow, NodeType::Bit);
            self.pc = self.pc_add(INSTRUCTION_SIZE);
        }

        self.new_comment("updating registers".to_string());
        for r in 1..NUMBER_OF_REGISTERS {
            self.current_nid = 60000000 + (r as u64);
            let reg = Register::from(r as u32);
            self.new_next(self.reg_node(reg), self.reg_flow(reg), NodeType::Word);
        }

        self.new_comment("updating dynamic dispatch flags".to_string());
        for r in 1..NUMBER_OF_REGISTERS {
            self.current_nid = 60000000 + (r as u64) * 10000;
            let reg = Register::from(r as u32);
            let mut control_flow = self.zero_bit.clone();
            for dynamic in self.dynamic.remove(0) {
                trace!(
                    "dynamic dispatch on {:?} at pc={:#x}",
                    reg,
                    dynamic.dispatch_address
                );
                let activate = &control_flow_update_nodes[&dynamic.dispatch_address];
                control_flow = self.control_flow_from_any(activate.clone(), control_flow);
            }
            self.new_next(self.dynamic_flag(reg), control_flow, NodeType::Bit);
        }

        self.new_comment("updating 64-bit virtual memory".to_string());
        self.current_nid = 70000000;
        self.new_next(
            self.memory_node.clone(),
            self.memory_flow.clone(),
            NodeType::Memory,
        );

        self.new_comment("checking syscall id".to_string());
        self.current_nid = 80000000;
        let not_openat = self.new_not_bit(is_openat);
        let not_read = self.new_not_bit(is_read);
        let not_write = self.new_not_bit(is_write);
        let not_exit = self.new_not_bit(is_exit);
        let not_brk = self.new_not_bit(is_brk);
        let check_syscall_and1 = self.new_and_bit(not_openat, not_read);
        let check_syscall_and2 = self.new_and_bit(check_syscall_and1, not_write);
        let check_syscall_and3 = self.new_and_bit(check_syscall_and2, not_exit);
        let check_syscall_and4 = self.new_and_bit(check_syscall_and3, not_brk);
        let check_syscall = self.new_and_bit(self.ecall_flow.clone(), check_syscall_and4);
        self.new_bad(check_syscall, "invalid-syscall-id");

        self.new_comment("checking segmentation faults".to_string());
        let data_start = self.new_const(self.data_range.start);
        let data_end = self.new_const(self.data_range.end);
        let heap_start = self.new_const(self.heap_range.start);
        let heap_max_end = self.new_const(self.heap_range.end);
        let stack_max_start = self.new_const(self.stack_range.start);
        let stack_end_inclusive = self.new_const(self.stack_range.end - 1);
        let below_data = self.new_ult(self.access_flow.clone(), data_start);
        self.new_bad(below_data, "memory-access-below-data");
        let above_data = self.new_ugte(self.access_flow.clone(), data_end);
        let below_heap = self.new_ult(self.access_flow.clone(), heap_start);
        let check_between1 = self.new_and_bit(above_data, below_heap);
        self.new_bad(check_between1, "memory-access-between-data-and-heap");
        let above_max_heap = self.new_ugte(self.access_flow.clone(), heap_max_end);
        let below_dyn_heap = self.new_ult(self.access_flow.clone(), brk_bump.clone());
        let check_between2 = self.new_and_bit(above_max_heap, below_dyn_heap);
        self.new_bad(check_between2, "memory-access-between-max-and-dyn-heap");
        let above_dyn_heap = self.new_ugte(self.access_flow.clone(), brk_bump);
        let below_dyn_stack = self.new_ult(self.access_flow.clone(), self.reg_node(Register::Sp));
        let check_between3 = self.new_and_bit(above_dyn_heap, below_dyn_stack);
        self.new_bad(check_between3, "memory-access-between-heap-and-stack");
        let above_dyn_stack = self.new_ugte(self.access_flow.clone(), self.reg_node(Register::Sp));
        let below_max_stack = self.new_ult(self.access_flow.clone(), stack_max_start);
        let check_between4 = self.new_and_bit(above_dyn_stack, below_max_stack);
        self.new_bad(check_between4, "memory-access-between-dyn-and-max-stack");
        let above_stack = self.new_ugt(self.access_flow.clone(), stack_end_inclusive);
        self.new_bad(above_stack, "memory-access-above-stack");

        self.new_comment("checking division and remainder by zero".to_string());
        let check_div = self.new_eq(self.division_flow.clone(), self.zero_word.clone());
        self.new_bad(check_div, "division-by-zero");
        let check_rem = self.new_eq(self.remainder_flow.clone(), self.zero_word.clone());
        self.new_bad(check_rem, "remainder-by-zero");

        self.new_comment("checking exit code".to_string());
        let check_exit_code = self.new_neq(self.reg_node(Register::A0), self.zero_word.clone());
        let check_exit = self.new_and_bit(active_exit, check_exit_code);
        self.new_bad(check_exit, "non-zero-exit-code");

        Ok(())
    }
}

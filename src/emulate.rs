use crate::engine::memory::VirtualMemory;
use crate::engine::system::{prepare_unix_stack, SyscallId, NUMBER_OF_REGISTERS, PAGE_SIZE};
use crate::util::next_multiple_of;
use byteorder::{ByteOrder, LittleEndian};
use log::{debug, info, trace, warn};
use riscu::{types::*, Instruction, Program, Register};
use std::cmp::min;
use std::fs::File;
use std::io::{self, Read, Stdin, Stdout, Write};
use std::mem::size_of;

//
// Public Interface
//

pub type EmulatorValue = u64;

#[derive(Debug)]
pub struct EmulatorState {
    registers: Vec<EmulatorValue>,
    memory: VirtualMemory<EmulatorValue>,
    program_counter: EmulatorValue,
    program_break: EmulatorValue,
    opened: Vec<File>,
    running: bool,
    stdin: Stdin,
    stdout: Stdout,
}

impl EmulatorState {
    pub fn new(memory_size: usize) -> Self {
        Self {
            registers: vec![0; NUMBER_OF_REGISTERS],
            memory: VirtualMemory::new(memory_size / riscu::WORD_SIZE, PAGE_SIZE),
            program_counter: 0,
            program_break: 0,
            opened: Vec::new(),
            running: false,
            stdin: io::stdin(),
            stdout: io::stdout(),
        }
    }

    // Fully bootstraps the emulator to allow execution of the given
    // `program` from its beginning with given arguments `argv`.
    pub fn bootstrap(&mut self, program: &Program, argv: &[String]) {
        let sp_value = self.memory.size() * riscu::WORD_SIZE;
        self.set_reg(Register::Sp, sp_value as u64);
        self.program_counter = initial_program_counter(program);
        self.program_break = initial_program_break(program);
        self.load_code_segment(program);
        self.load_data_segment(program);
        self.load_stack_segment(argv);
    }

    // Partially prepares the emulator with the code segment from the
    // given `program`. This can be used in conjunction with other
    // mechanisms that restore the rest of the machine state.
    pub fn prepare(&mut self, program: &Program) {
        self.load_code_segment(program);
    }

    // Start emulation.
    pub fn run(&mut self) {
        self.running = true;
        while self.running {
            let fetched = fetch(self);
            let decoded = decode(fetched);
            execute(self, decoded);
        }
    }
}

//
// Private Implementation
//

const INSTRUCTION_SIZE_MASK: u64 = riscu::INSTRUCTION_SIZE as u64 - 1;
const WORD_SIZE_MASK: u64 = riscu::WORD_SIZE as u64 - 1;
const MAX_FILENAME_LENGTH: usize = 128;
const FIRST_REAL_FD: usize = 3;

fn initial_program_counter(program: &Program) -> EmulatorValue {
    program.instruction_range.start
}

fn initial_program_break(program: &Program) -> EmulatorValue {
    let data_size = program.data.content.len();
    let data_end = program.data.address + data_size as u64;
    next_multiple_of(data_end, PAGE_SIZE as u64)
}

impl EmulatorState {
    fn pc_add(&mut self, imm: u64) {
        self.program_counter = self.program_counter.wrapping_add(imm);
    }

    fn pc_next(&mut self) {
        self.pc_add(riscu::INSTRUCTION_SIZE as u64);
    }

    // TODO: Move to public portion of file.
    pub fn pc_set(&mut self, val: EmulatorValue) {
        assert!(val & INSTRUCTION_SIZE_MASK == 0, "program counter aligned");
        self.program_counter = val;
    }

    // TODO: Move to public portion of file.
    pub fn get_reg(&self, reg: Register) -> EmulatorValue {
        self.registers[reg as usize]
    }

    // TODO: Move to public portion of file.
    pub fn set_reg(&mut self, reg: Register, val: EmulatorValue) {
        assert!(reg != Register::Zero, "cannot set `zero` register");
        self.registers[reg as usize] = val;
    }

    fn set_reg_maybe(&mut self, reg: Register, val: EmulatorValue) {
        if reg == Register::Zero {
            return;
        };
        self.set_reg(reg, val);
    }

    // TODO: Move to public portion of file.
    pub fn get_mem(&self, adr: EmulatorValue) -> EmulatorValue {
        assert!(adr & WORD_SIZE_MASK == 0, "address aligned");
        self.memory[adr as usize / riscu::WORD_SIZE]
    }

    fn get_mem_typed<T: MyLittleEndian>(&self, adr: EmulatorValue) -> T {
        assert!(adr % (size_of::<T>() as u64) == 0, "address aligned");
        let word_address = adr & !WORD_SIZE_MASK;
        let word_offset = (adr & WORD_SIZE_MASK) as usize;
        let bytes = self.get_mem(word_address).to_le_bytes();
        MyLittleEndian::read(&bytes[word_offset..])
    }

    // TODO: Move to public portion of file.
    pub fn set_mem(&mut self, adr: EmulatorValue, val: EmulatorValue) {
        assert!(adr & WORD_SIZE_MASK == 0, "address aligned");
        self.memory[adr as usize / riscu::WORD_SIZE] = val;
    }

    fn set_mem_typed<T: MyLittleEndian>(&mut self, adr: EmulatorValue, val: T) {
        assert!(adr % (size_of::<T>() as u64) == 0, "address aligned");
        let word_address = adr & !WORD_SIZE_MASK;
        let word_offset = (adr & WORD_SIZE_MASK) as usize;
        let mut bytes = self.get_mem(word_address).to_le_bytes();
        MyLittleEndian::write(&mut bytes[word_offset..], val);
        let word = EmulatorValue::from_le_bytes(bytes);
        self.set_mem(word_address, word);
    }

    fn copy_mem(&mut self, adr: EmulatorValue, src: &[u8]) {
        src.iter()
            .zip(adr..)
            .for_each(|(b, a)| self.set_mem_typed::<u8>(a, *b));
    }

    fn load_code_segment(&mut self, program: &Program) {
        self.copy_mem(program.code.address, &program.code.content);
    }

    fn load_data_segment(&mut self, program: &Program) {
        self.copy_mem(program.data.address, &program.data.content);
    }

    fn load_stack_segment(&mut self, argv: &[String]) {
        debug!("argc: {}, argv: {:?}", argv.len(), argv);
        for val in prepare_unix_stack(argv, self.get_reg(Register::Sp)) {
            let sp = self.get_reg(Register::Sp) - riscu::WORD_SIZE as u64;
            self.set_reg(Register::Sp, sp);
            self.set_mem(sp, val);
        }
    }

    // TODO: Move to public portion of file.
    pub fn get_program_counter(&self) -> EmulatorValue {
        self.program_counter
    }

    // TODO: Move to public portion of file.
    pub fn get_program_break(&self) -> EmulatorValue {
        self.program_break
    }

    // TODO: Move to public portion of file.
    pub fn set_program_break(&mut self, val: EmulatorValue) {
        assert!(val & WORD_SIZE_MASK == 0, "program break aligned");
        assert!(val >= self.program_break, "monotonic");
        self.program_break = val;
    }

    fn fd_new(&mut self, file: File) -> EmulatorValue {
        let fd = self.opened.len() + FIRST_REAL_FD;
        self.opened.push(file);
        fd as EmulatorValue
    }

    fn fd_read(&mut self, fd: EmulatorValue) -> &mut dyn Read {
        match fd {
            0 => &mut self.stdin,
            1 => panic!("reading from `stdout` is a bad idea"),
            2 => panic!("reading from `stderr` is a bad idea"),
            _ => &mut self.opened[fd as usize - FIRST_REAL_FD],
        }
    }

    fn fd_write(&mut self, fd: EmulatorValue) -> &mut dyn Write {
        match fd {
            0 => panic!("writing to `stdin` is a bad idea"),
            1 => &mut self.stdout,
            2 => unimplemented!("writing to `stderr` missing"),
            _ => &mut self.opened[fd as usize - FIRST_REAL_FD],
        }
    }
}

fn fetch(state: &mut EmulatorState) -> u32 {
    assert!(state.program_counter & INSTRUCTION_SIZE_MASK == 0);
    assert!(riscu::INSTRUCTION_SIZE == size_of::<u32>());
    state.get_mem_typed::<u32>(state.program_counter)
}

fn decode(instruction_half_word: u32) -> Instruction {
    riscu::decode(instruction_half_word).expect("valid instruction")
}

fn execute(state: &mut EmulatorState, instr: Instruction) {
    match instr {
        Instruction::Lui(utype) => exec_lui(state, utype),
        Instruction::Auipc(utype) => exec_auipc(state, utype),
        Instruction::Jal(jtype) => exec_jal(state, jtype),
        Instruction::Jalr(itype) => exec_jalr(state, itype),
        Instruction::Beq(btype) => exec_beq(state, btype),
        Instruction::Bne(btype) => exec_bne(state, btype),
        Instruction::Blt(btype) => exec_blt(state, btype),
        Instruction::Bge(btype) => exec_bge(state, btype),
        Instruction::Bltu(btype) => exec_bltu(state, btype),
        Instruction::Bgeu(btype) => exec_bgeu(state, btype),
        Instruction::Lb(itype) => exec_lb(state, itype),
        Instruction::Lh(itype) => exec_lh(state, itype),
        Instruction::Lw(itype) => exec_lw(state, itype),
        Instruction::Ld(itype) => exec_ld(state, itype),
        Instruction::Lbu(itype) => exec_lbu(state, itype),
        Instruction::Lhu(itype) => exec_lhu(state, itype),
        Instruction::Sb(stype) => exec_sb(state, stype),
        Instruction::Sh(stype) => exec_sh(state, stype),
        Instruction::Sw(stype) => exec_sw(state, stype),
        Instruction::Sd(stype) => exec_sd(state, stype),
        Instruction::Addi(itype) => exec_addi(state, itype),
        Instruction::Sltiu(itype) => exec_sltiu(state, itype),
        Instruction::Xori(itype) => exec_xori(state, itype),
        Instruction::Ori(itype) => exec_ori(state, itype),
        Instruction::Andi(itype) => exec_andi(state, itype),
        Instruction::Slli(itype) => exec_slli(state, itype),
        Instruction::Srli(itype) => exec_srli(state, itype),
        Instruction::Srai(itype) => exec_srai(state, itype),
        Instruction::Addiw(itype) => exec_addiw(state, itype),
        Instruction::Slliw(itype) => exec_slliw(state, itype),
        Instruction::Srliw(itype) => exec_srliw(state, itype),
        Instruction::Sraiw(itype) => exec_sraiw(state, itype),
        Instruction::Add(rtype) => exec_add(state, rtype),
        Instruction::Sub(rtype) => exec_sub(state, rtype),
        Instruction::Sll(rtype) => exec_sll(state, rtype),
        Instruction::Slt(rtype) => exec_slt(state, rtype),
        Instruction::Sltu(rtype) => exec_sltu(state, rtype),
        Instruction::Srl(rtype) => exec_srl(state, rtype),
        Instruction::Sra(rtype) => exec_sra(state, rtype),
        Instruction::Or(rtype) => exec_or(state, rtype),
        Instruction::And(rtype) => exec_and(state, rtype),
        Instruction::Mul(rtype) => exec_mul(state, rtype),
        Instruction::Div(rtype) => exec_div(state, rtype),
        Instruction::Divu(rtype) => exec_divu(state, rtype),
        Instruction::Rem(rtype) => exec_rem(state, rtype),
        Instruction::Remu(rtype) => exec_remu(state, rtype),
        Instruction::Addw(rtype) => exec_addw(state, rtype),
        Instruction::Subw(rtype) => exec_subw(state, rtype),
        Instruction::Sllw(rtype) => exec_sllw(state, rtype),
        Instruction::Mulw(rtype) => exec_mulw(state, rtype),
        Instruction::Divw(rtype) => exec_divw(state, rtype),
        Instruction::Remw(rtype) => exec_remw(state, rtype),
        Instruction::Ecall(_itype) => exec_ecall(state),
        // TODO: Cover all needed instructions here.
        _ => unimplemented!("not implemented: {:?}", instr),
    }
}

//
// RISC-V Instruction Semantics
//
// The following functions each codify the semantics of one RISC-V
// instruction in terms of a given `EmulatorState`. Above each function
// is a comment providing an informal description of the semantics. The
// following conventions are used in these comments:
//   - All registers and 'mem[x]' locations have 64 bit width.
//   - Some operators are suffixed with 's' and 'u' to distinguish the
//     difference between signed and unsigned variants, e.g. '<u', '<s'.
//   - The bit width of operators is determined by their operands.
//   - Any sign extension (sext) or zero extension (zext) denotes the
//     target bit width explicitly, e.g. 's64(x)', 'z64(x)', 's32(x)'
//   - Reduction of bit with is denoted in braces, e.g. rs1{32}, and
//     indicates selecting the given number of least-significant bits,
//     or used to make implicit bit widths explicit, e.g. imm{12}.
//   - Memory access of smaller bit width uses, e.g. mem16[x], mem8[x].
//   - Memory is always byte-addressed, independent of the bit width.
//

// rd = s64(imm{20}) << 12
// pc = pc + 4
fn exec_lui(state: &mut EmulatorState, utype: UType) {
    let rd_value = ((utype.imm() as i32) << 12) as u64;
    trace_utype(state, "lui", utype, rd_value);
    state.set_reg(utype.rd(), rd_value);
    state.pc_next();
}

// rd = pc + s64(imm{20}) << 12
// pc = pc + 4
fn exec_auipc(state: &mut EmulatorState, utype: UType) {
    let rd_value = ((utype.imm() as i32) << 12) as u64 + state.program_counter;
    trace_utype(state, "auipc", utype, rd_value);
    state.set_reg(utype.rd(), rd_value);
    state.pc_next();
}

// rd = pc + 4
// pc = pc + s64(imm)
fn exec_jal(state: &mut EmulatorState, jtype: JType) {
    let rd_value = state.program_counter + riscu::INSTRUCTION_SIZE as u64;
    trace_jtype(state, "jal", jtype, rd_value);
    state.set_reg_maybe(jtype.rd(), rd_value);
    state.pc_add(jtype.imm() as u64);
}

// rd = pc + 4
// pc = rs1 + s64(imm)
fn exec_jalr(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = state.program_counter + riscu::INSTRUCTION_SIZE as u64;
    let pc_value = rs1_value.wrapping_add(itype.imm() as u64);
    trace_itype(state, "jalr", itype, rd_value);
    state.set_reg_maybe(itype.rd(), rd_value);
    state.pc_set(pc_value);
}

// pc = pc + s64(imm)         ||| if (rs1 == rs2)
// pc = pc + 4                ||| otherwise
fn exec_beq(state: &mut EmulatorState, btype: BType) {
    let rs1_value = state.get_reg(btype.rs1());
    let rs2_value = state.get_reg(btype.rs2());
    let condition = rs1_value == rs2_value;
    trace_btype(state, "beq", btype, condition);
    if condition {
        state.pc_add(btype.imm() as u64);
    } else {
        state.pc_next();
    }
}

// pc = pc + s64(imm)         ||| if (rs1 != rs2)
// pc = pc + 4                ||| otherwise
fn exec_bne(state: &mut EmulatorState, btype: BType) {
    let rs1_value = state.get_reg(btype.rs1());
    let rs2_value = state.get_reg(btype.rs2());
    let condition = rs1_value != rs2_value;
    trace_btype(state, "bne", btype, condition);
    if condition {
        state.pc_add(btype.imm() as u64);
    } else {
        state.pc_next();
    }
}

// pc = pc + s64(imm)         ||| if (rs1 <s rs2)
// pc = pc + 4                ||| otherwise
fn exec_blt(state: &mut EmulatorState, btype: BType) {
    let rs1_value = state.get_reg(btype.rs1());
    let rs2_value = state.get_reg(btype.rs2());
    let condition = (rs1_value as i64) < (rs2_value as i64);
    trace_btype(state, "blt", btype, condition);
    if condition {
        state.pc_add(btype.imm() as u64);
    } else {
        state.pc_next();
    }
}

// pc = pc + s64(imm)         ||| if (rs1 >=s rs2)
// pc = pc + 4                ||| otherwise
fn exec_bge(state: &mut EmulatorState, btype: BType) {
    let rs1_value = state.get_reg(btype.rs1());
    let rs2_value = state.get_reg(btype.rs2());
    let condition = (rs1_value as i64) >= (rs2_value as i64);
    trace_btype(state, "bge", btype, condition);
    if condition {
        state.pc_add(btype.imm() as u64);
    } else {
        state.pc_next();
    }
}

// pc = pc + s64(imm)         ||| if (rs1 <u rs2)
// pc = pc + 4                ||| otherwise
fn exec_bltu(state: &mut EmulatorState, btype: BType) {
    let rs1_value = state.get_reg(btype.rs1());
    let rs2_value = state.get_reg(btype.rs2());
    let condition = rs1_value < rs2_value;
    trace_btype(state, "bltu", btype, condition);
    if condition {
        state.pc_add(btype.imm() as u64);
    } else {
        state.pc_next();
    }
}

// pc = pc + s64(imm)         ||| if (rs1 >=u rs2)
// pc = pc + 4                ||| otherwise
fn exec_bgeu(state: &mut EmulatorState, btype: BType) {
    let rs1_value = state.get_reg(btype.rs1());
    let rs2_value = state.get_reg(btype.rs2());
    let condition = rs1_value >= rs2_value;
    trace_btype(state, "bgeu", btype, condition);
    if condition {
        state.pc_add(btype.imm() as u64);
    } else {
        state.pc_next();
    }
}

// rd = s64(mem8[rs1 + s64(imm{12})])
// pc = pc + 4
fn exec_lb(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let address = rs1_value.wrapping_add(itype.imm() as u64);
    let rd_value = state.get_mem_typed::<i8>(address) as u64;
    trace_itype(state, "lb", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = z64(mem8[rs1 + s64(imm{12})])
// pc = pc + 4
fn exec_lbu(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let address = rs1_value.wrapping_add(itype.imm() as u64);
    let rd_value = state.get_mem_typed::<u8>(address) as u64;
    trace_itype(state, "lbu", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(mem16[rs1 + s64(imm{12})])
// pc = pc + 4
fn exec_lh(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let address = rs1_value.wrapping_add(itype.imm() as u64);
    let rd_value = state.get_mem_typed::<i16>(address) as u64;
    trace_itype(state, "lh", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = z64(mem16[rs1 + s64(imm{12})])
// pc = pc + 4
fn exec_lhu(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let address = rs1_value.wrapping_add(itype.imm() as u64);
    let rd_value = state.get_mem_typed::<u16>(address) as u64;
    trace_itype(state, "lhu", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(mem32[rs1 + s64(imm{12})])
// pc = pc + 4
fn exec_lw(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let address = rs1_value.wrapping_add(itype.imm() as u64);
    let rd_value = state.get_mem_typed::<i32>(address) as u64;
    trace_itype(state, "lw", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = mem[rs1 + s64(imm{12})]
// pc = pc + 4
fn exec_ld(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let address = rs1_value.wrapping_add(itype.imm() as u64);
    let rd_value = state.get_mem(address);
    trace_itype(state, "ld", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// mem8[rs1 + s64(imm{12})] = rs2{8}
// pc = pc + 4
fn exec_sb(state: &mut EmulatorState, stype: SType) {
    let rs1_value = state.get_reg(stype.rs1());
    let rs2_value = state.get_reg(stype.rs2());
    let address = rs1_value.wrapping_add(stype.imm() as u64);
    trace_stype(state, "sb", stype, address);
    state.set_mem_typed::<u8>(address, rs2_value as u8);
    state.pc_next();
}

// mem16[rs1 + s64(imm{12})] = rs2{16}
// pc = pc + 4
fn exec_sh(state: &mut EmulatorState, stype: SType) {
    let rs1_value = state.get_reg(stype.rs1());
    let rs2_value = state.get_reg(stype.rs2());
    let address = rs1_value.wrapping_add(stype.imm() as u64);
    trace_stype(state, "sh", stype, address);
    state.set_mem_typed::<u16>(address, rs2_value as u16);
    state.pc_next();
}

// mem32[rs1 + s64(imm{12})] = rs2{32}
// pc = pc + 4
fn exec_sw(state: &mut EmulatorState, stype: SType) {
    let rs1_value = state.get_reg(stype.rs1());
    let rs2_value = state.get_reg(stype.rs2());
    let address = rs1_value.wrapping_add(stype.imm() as u64);
    trace_stype(state, "sw", stype, address);
    state.set_mem_typed::<u32>(address, rs2_value as u32);
    state.pc_next();
}

// mem[rs1 + s64(imm{12})] = rs2
// pc = pc + 4
fn exec_sd(state: &mut EmulatorState, stype: SType) {
    let rs1_value = state.get_reg(stype.rs1());
    let rs2_value = state.get_reg(stype.rs2());
    let address = rs1_value.wrapping_add(stype.imm() as u64);
    trace_stype(state, "sd", stype, address);
    state.set_mem(address, rs2_value);
    state.pc_next();
}

// rd = rs1 + s64(imm{12})
// pc = pc + 4
fn exec_addi(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = rs1_value.wrapping_add(itype.imm() as u64);
    trace_itype(state, "addi", itype, rd_value);
    state.set_reg_maybe(itype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} + s32(imm{12}))
// pc = pc + 4
fn exec_addiw(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = (rs1_value as i32).wrapping_add(itype.imm()) as u64;
    trace_itype(state, "addiw", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = 1                     ||| if (rs1 <u s64(imm{12}))
// rd = 0                     ||| otherwise
// pc = pc + 4
fn exec_sltiu(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let condition = rs1_value < (itype.imm() as u64);
    let rd_value = EmulatorValue::from(condition);
    trace_itype(state, "sltiu", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 ^ s64(imm{12})
// pc = pc + 4
fn exec_xori(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = rs1_value ^ (itype.imm() as u64);
    trace_itype(state, "xori", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 | s64(imm{12})
// pc = pc + 4
fn exec_ori(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = rs1_value | (itype.imm() as u64);
    trace_itype(state, "ori", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 & s64(imm{12})
// pc = pc + 4
fn exec_andi(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = rs1_value & (itype.imm() as u64);
    trace_itype(state, "andi", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 << z32(imm{6})
// pc = pc + 4
fn exec_slli(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = rs1_value.wrapping_shl(itype.imm() as u32);
    trace_itype(state, "slli", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} << z32(imm{5}))
// pc = pc + 4
fn exec_slliw(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = (rs1_value as i32).wrapping_shl(itype.imm() as u32) as u64;
    trace_itype(state, "slliw", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 >>u z32(imm{6})
// pc = pc + 4
fn exec_srli(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = rs1_value.wrapping_shr(itype.imm() as u32);
    trace_itype(state, "srli", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} >>u z32(imm{5}))
// pc = pc + 4
fn exec_srliw(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = (rs1_value as u32).wrapping_shr(itype.imm() as u32) as i32 as u64;
    trace_itype(state, "srliw", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 >>s z32(imm{6})
// pc = pc + 4
fn exec_srai(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = (rs1_value as i64).wrapping_shr(itype.imm() as u32) as u64;
    trace_itype(state, "srai", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} >>s z32(imm{5}))
// pc = pc + 4
fn exec_sraiw(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = (rs1_value as i32).wrapping_shr(itype.imm() as u32) as u64;
    trace_itype(state, "sraiw", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 + rs2
// pc = pc + 4
fn exec_add(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_add(rs2_value);
    trace_rtype(state, "add", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} + rs2{32})
// pc = pc + 4
fn exec_addw(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = (rs1_value as i32).wrapping_add(rs2_value as i32) as u64;
    trace_rtype(state, "addw", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 - rs2
// pc = pc + 4
fn exec_sub(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_sub(rs2_value);
    trace_rtype(state, "sub", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} - rs2{32})
// pc = pc + 4
fn exec_subw(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = (rs1_value as i32).wrapping_sub(rs2_value as i32) as u64;
    trace_rtype(state, "subw", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 << z32(rs2{6})
// pc = pc + 4
fn exec_sll(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_shl(rs2_value as u32);
    trace_rtype(state, "sll", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} << z32(rs2{5}))
// pc = pc + 4
fn exec_sllw(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = (rs1_value as i32).wrapping_shl(rs2_value as u32) as u64;
    trace_rtype(state, "sllw", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 >>u z32(rs2{6})
// pc = pc + 4
fn exec_srl(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_shr(rs2_value as u32);
    trace_rtype(state, "srl", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 >>s z32(rs2{6})
// pc = pc + 4
fn exec_sra(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = (rs1_value as i64).wrapping_shr(rs2_value as u32) as u64;
    trace_rtype(state, "sra", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = 1                     ||| if (rs1 < rs2)
// rd = 0                     ||| otherwise
// pc = pc + 4
fn exec_slt(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let condition = (rs1_value as i64) < (rs2_value as i64);
    let rd_value = EmulatorValue::from(condition);
    trace_rtype(state, "slt", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = 1                     ||| if (rs1 <u rs2)
// rd = 0                     ||| otherwise
// pc = pc + 4
fn exec_sltu(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let condition = rs1_value < rs2_value;
    let rd_value = EmulatorValue::from(condition);
    trace_rtype(state, "sltu", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 | rs2
// pc = pc + 4
fn exec_or(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value | rs2_value;
    trace_rtype(state, "or", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 & rs2
// pc = pc + 4
fn exec_and(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value & rs2_value;
    trace_rtype(state, "and", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 * rs2
// pc = pc + 4
fn exec_mul(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_mul(rs2_value);
    trace_rtype(state, "mul", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} * rs2{32})
// pc = pc + 4
fn exec_mulw(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = (rs1_value as i32).wrapping_mul(rs2_value as i32) as u64;
    trace_rtype(state, "mulw", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 / rs2
// pc = pc + 4
fn exec_div(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    assert!(rs2_value != 0, "check for non-zero divisor");
    let rd_value = (rs1_value as i64).wrapping_div(rs2_value as i64) as u64;
    trace_rtype(state, "div", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} / rs2{32})
// pc = pc + 4
fn exec_divw(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    assert!(rs2_value != 0, "check for non-zero divisor");
    let rd_value = (rs1_value as i32).wrapping_div(rs2_value as i32) as u64;
    trace_rtype(state, "divw", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 /u rs2
// pc = pc + 4
fn exec_divu(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    assert!(rs2_value != 0, "check for non-zero divisor");
    let rd_value = rs1_value.wrapping_div(rs2_value);
    trace_rtype(state, "divu", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 % rs2
// pc = pc + 4
fn exec_rem(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    assert!(rs2_value != 0, "check for non-zero divisor");
    let rd_value = (rs1_value  as i64).wrapping_rem(rs2_value  as i64)  as u64;
    trace_rtype(state, "rem", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = s64(rs1{32} % rs2{32})
// pc = pc + 4
fn exec_remw(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    assert!(rs2_value != 0, "check for non-zero divisor");
    let rd_value = (rs1_value  as i32).wrapping_rem(rs2_value  as i32)  as u64;
    trace_rtype(state, "remw", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

// rd = rs1 %u rs2
// pc = pc + 4
fn exec_remu(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    assert!(rs2_value != 0, "check for non-zero divisor");
    let rd_value = rs1_value.wrapping_rem(rs2_value);
    trace_rtype(state, "remu", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

fn exec_ecall(state: &mut EmulatorState) {
    let a7_value = state.get_reg(Register::A7);
    if a7_value == SyscallId::Exit as u64 {
        let exit_code = state.get_reg(Register::A0);
        println!(); // print empty newline to clean up
        io::stdout().flush().expect("stdout flush success");
        info!("program exiting with exit code {}", exit_code);
        state.running = false;
    } else if a7_value == SyscallId::Read as u64 {
        syscall_read(state);
    } else if a7_value == SyscallId::Write as u64 {
        syscall_write(state);
    } else if a7_value == SyscallId::Open as u64 {
        syscall_open(state);
    } else if a7_value == SyscallId::Openat as u64 {
        syscall_openat(state);
    } else if a7_value == SyscallId::Brk as u64 {
        syscall_brk(state);
    } else if a7_value == SyscallId::Close as u64 {
        // TODO close system call
    } else if a7_value == SyscallId::Newfstat as u64 {
        // TODO newfstat system call
    } else {
        warn!("unknown system call: {}", a7_value);
        state.set_reg(Register::A0, u64::MAX);
    }
    state.pc_next();
}

fn syscall_read(state: &mut EmulatorState) {
    let fd = state.get_reg(Register::A0);
    let buffer = state.get_reg(Register::A1);
    let size = state.get_reg(Register::A2);

    // Check provided address is valid, iterate through the buffer word
    // by word, and emulate `read` system call via `std::io::Read`.
    assert!(buffer & WORD_SIZE_MASK == 0, "buffer pointer aligned");
    let mut total_bytes = 0; // counts total bytes read
    let mut tmp_buffer: Vec<u8> = vec![0; 8]; // scratch buffer
    for adr in (buffer..buffer + size).step_by(riscu::WORD_SIZE) {
        let bytes_to_read = min(size as usize - total_bytes, riscu::WORD_SIZE);
        LittleEndian::write_u64(&mut tmp_buffer, state.get_mem(adr));
        let bytes = &mut tmp_buffer[0..bytes_to_read]; // only for safety
        let bytes_read = state.fd_read(fd).read(bytes).expect("read success");
        state.set_mem(adr, LittleEndian::read_u64(&tmp_buffer));
        total_bytes += bytes_read; // tally all bytes
        if bytes_read != bytes_to_read {
            break;
        }
    }
    let result = total_bytes as u64;

    state.set_reg(Register::A0, result);
    debug!("read({},{:#x},{}) -> {}", fd, buffer, size, result);
}

fn syscall_write(state: &mut EmulatorState) {
    let fd = state.get_reg(Register::A0);
    let buffer = state.get_reg(Register::A1);
    let size = state.get_reg(Register::A2);

    // Check provided address is valid, iterate through the buffer word
    // by word, and emulate `write` system call via `std::io::Write`.
    assert!(buffer & WORD_SIZE_MASK == 0, "buffer pointer aligned");
    let mut total_bytes = 0; // counts total bytes written
    for adr in (buffer..buffer + size).step_by(riscu::WORD_SIZE) {
        let bytes_to_write = min(size as usize - total_bytes, riscu::WORD_SIZE);
        let bytes = &state.get_mem(adr).to_le_bytes()[0..bytes_to_write];
        let bytes_written = state.fd_write(fd).write(bytes).expect("write success");
        total_bytes += bytes_written; // tally all bytes
        if bytes_written != bytes_to_write {
            break;
        }
    }
    let result = total_bytes as u64;

    state.set_reg(Register::A0, result);
    debug!("write({},{:#x},{}) -> {}", fd, buffer, size, result);
}

fn syscall_open(state: &mut EmulatorState) {
    let path = state.get_reg(Register::A0);
    let flag = state.get_reg(Register::A1);
    let mode = state.get_reg(Register::A2);
    let temp = state.get_reg(Register::A3);

    // TODO Set fd to AT_FDCWD
    // state.set_reg(Register::A0, AT_FDCWD);
    state.set_reg(Register::A1, path);
    state.set_reg(Register::A2, flag);
    state.set_reg(Register::A3, mode);

    syscall_openat(state);

    // needed?
    state.set_reg(Register::A1, flag);
    state.set_reg(Register::A2, mode);
    state.set_reg(Register::A3, temp);
}

fn syscall_openat(state: &mut EmulatorState) {
    let fd = state.get_reg(Register::A0);
    let path = state.get_reg(Register::A1);
    let flag = state.get_reg(Register::A2);
    let mode = state.get_reg(Register::A3);

    // Check provided address is valid, copy path name from memory into
    // a string, and emulate `openat` system call via `File::open`.
    assert!(path & WORD_SIZE_MASK == 0, "path pointer aligned");
    let mut path_buffer: Vec<u8> = vec![0; MAX_FILENAME_LENGTH];
    for i in (0..MAX_FILENAME_LENGTH).step_by(riscu::WORD_SIZE) {
        let chunk = &mut path_buffer[i..i + 8];
        LittleEndian::write_u64(chunk, state.get_mem(path + i as u64));
        if let Some(j) = chunk.iter().position(|x| *x == 0) {
            path_buffer.truncate(i + j);
            break;
        }
    }
    let path_string = String::from_utf8(path_buffer).expect("valid UTF-8 string");
    let file = File::open(path_string).expect("open success");
    let result = state.fd_new(file);

    state.set_reg(Register::A0, result);
    debug!("openat({},{:#x},{},{}) -> {}", fd, path, flag, mode, result);
}

fn syscall_brk(state: &mut EmulatorState) {
    let address = state.get_reg(Register::A0);

    // Check provided address is valid and falls between the current
    // program break (highest heap) and `sp` register (lowest stack).
    assert!(address & WORD_SIZE_MASK == 0, "program break aligned");
    if (address >= state.program_break) && (address < state.get_reg(Register::Sp)) {
        state.set_program_break(address);
    }
    let result = state.program_break;

    state.set_reg(Register::A0, result);
    debug!("brk({:#x}) -> {:#x}", address, result);
}

fn trace_btype(state: &EmulatorState, mne: &str, btype: BType, condition: bool) {
    trace!(
        "pc={:#x}: {} {:?},{:?},{}: {:?}={:#x}, {:?}={:#x} |- {}",
        state.program_counter,
        mne,
        btype.rs1(),
        btype.rs2(),
        btype.imm(),
        btype.rs1(),
        state.get_reg(btype.rs1()),
        btype.rs2(),
        state.get_reg(btype.rs2()),
        condition
    );
}

fn trace_itype(state: &EmulatorState, mne: &str, itype: IType, rd_value: EmulatorValue) {
    trace!(
        "pc={:#x}: {} {:?},{:?},{}: {:?}={:#x} |- {:?}={:#x} -> {:?}={:#x}",
        state.program_counter,
        mne,
        itype.rd(),
        itype.rs1(),
        itype.imm(),
        itype.rs1(),
        state.get_reg(itype.rs1()),
        itype.rd(),
        state.get_reg(itype.rd()),
        itype.rd(),
        rd_value
    );
}

fn trace_jtype(state: &EmulatorState, mne: &str, jtype: JType, rd_value: EmulatorValue) {
    trace!(
        "pc={:#x}: {} {:?},{}: |- {:?}={:#x} -> {:?}={:#x}",
        state.program_counter,
        mne,
        jtype.rd(),
        jtype.imm(),
        jtype.rd(),
        state.get_reg(jtype.rd()),
        jtype.rd(),
        rd_value
    );
}

fn trace_rtype(state: &EmulatorState, mne: &str, rtype: RType, rd_value: EmulatorValue) {
    trace!(
        "pc={:#x}: {} {:?},{:?},{:?}: {:?}={:#x}, {:?}={:#x} |- {:?}={:#x} -> {:?}={:#x}",
        state.program_counter,
        mne,
        rtype.rd(),
        rtype.rs1(),
        rtype.rs2(),
        rtype.rs1(),
        state.get_reg(rtype.rs1()),
        rtype.rs2(),
        state.get_reg(rtype.rs2()),
        rtype.rd(),
        state.get_reg(rtype.rd()),
        rtype.rd(),
        rd_value
    );
}

fn trace_stype(state: &EmulatorState, mne: &str, stype: SType, address: EmulatorValue) {
    trace!(
        "pc={:#x}: {} {:?},{}({:?}): {:?}={:#x}, {:?}={:#x} |- mem[{:#x}]=? -> mem[{:#x}]=?",
        state.program_counter,
        mne,
        stype.rs2(),
        stype.imm(),
        stype.rs1(),
        stype.rs1(),
        state.get_reg(stype.rs1()),
        stype.rs2(),
        state.get_reg(stype.rs2()),
        address & !WORD_SIZE_MASK,
        address & !WORD_SIZE_MASK,
    );
}

fn trace_utype(state: &EmulatorState, mne: &str, utype: UType, rd_value: EmulatorValue) {
    trace!(
        "pc={:#x}: {} {:?},{:#x}: |- {:?}={:#x} -> {:?}={:#x}",
        state.program_counter,
        mne,
        utype.rd(),
        utype.imm(),
        utype.rd(),
        state.get_reg(utype.rd()),
        utype.rd(),
        rd_value
    );
}

trait MyLittleEndian {
    fn write(bytes: &mut [u8], value: Self);
    fn read(bytes: &[u8]) -> Self;
}

impl MyLittleEndian for i8 {
    fn write(bytes: &mut [u8], value: Self) {
        bytes[0] = value as u8;
    }
    fn read(bytes: &[u8]) -> Self {
        bytes[0] as i8
    }
}

impl MyLittleEndian for u8 {
    fn write(bytes: &mut [u8], value: Self) {
        bytes[0] = value;
    }
    fn read(bytes: &[u8]) -> Self {
        bytes[0]
    }
}

impl MyLittleEndian for i16 {
    fn write(bytes: &mut [u8], value: Self) {
        LittleEndian::write_i16(bytes, value);
    }
    fn read(bytes: &[u8]) -> Self {
        LittleEndian::read_i16(bytes)
    }
}

impl MyLittleEndian for u16 {
    fn write(bytes: &mut [u8], value: Self) {
        LittleEndian::write_u16(bytes, value);
    }
    fn read(bytes: &[u8]) -> Self {
        LittleEndian::read_u16(bytes)
    }
}

impl MyLittleEndian for i32 {
    fn write(bytes: &mut [u8], value: Self) {
        LittleEndian::write_i32(bytes, value);
    }
    fn read(bytes: &[u8]) -> Self {
        LittleEndian::read_i32(bytes)
    }
}

impl MyLittleEndian for u32 {
    fn write(bytes: &mut [u8], value: Self) {
        LittleEndian::write_u32(bytes, value);
    }
    fn read(bytes: &[u8]) -> Self {
        LittleEndian::read_u32(bytes)
    }
}

use crate::engine::memory::VirtualMemory;
use crate::engine::system::{SyscallId, NUMBER_OF_REGISTERS, PAGE_SIZE};
use crate::util::next_multiple_of;
use byteorder::{ByteOrder, LittleEndian};
use log::{debug, info, trace};
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
        self.program_counter = program.code.address;
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

    fn get_reg(&self, reg: Register) -> EmulatorValue {
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

    fn get_mem(&self, adr: EmulatorValue) -> EmulatorValue {
        assert!(adr & WORD_SIZE_MASK == 0, "address aligned");
        self.memory[adr as usize / riscu::WORD_SIZE]
    }

    fn get_mem_maybe(&self, adr: EmulatorValue) -> Option<EmulatorValue> {
        assert!(adr & WORD_SIZE_MASK == 0, "address aligned");
        if adr as usize >= self.memory.size() {
            return None;
        }
        Some(self.get_mem(adr))
    }

    // TODO: Move to public portion of file.
    pub fn set_mem(&mut self, adr: EmulatorValue, val: EmulatorValue) {
        assert!(adr & WORD_SIZE_MASK == 0, "address aligned");
        self.memory[adr as usize / riscu::WORD_SIZE] = val;
    }

    fn push_stack(&mut self, val: EmulatorValue) {
        let sp = self.get_reg(Register::Sp) - riscu::WORD_SIZE as u64;
        self.set_reg(Register::Sp, sp);
        self.set_mem(sp, val);
    }

    fn load_code_segment(&mut self, program: &Program) {
        assert!(program.code.content.len() % riscu::WORD_SIZE == 0);
        for (i, buf) in program.code.content.chunks(riscu::WORD_SIZE).enumerate() {
            let adr = program.code.address as usize + i * riscu::WORD_SIZE;
            let val = LittleEndian::read_u64(buf);
            self.set_mem(adr as u64, val);
        }
    }

    fn load_data_segment(&mut self, program: &Program) {
        assert!(program.data.content.len() % riscu::WORD_SIZE == 0);
        for (i, buf) in program.data.content.chunks(riscu::WORD_SIZE).enumerate() {
            let adr = program.data.address as usize + i * riscu::WORD_SIZE;
            let val = LittleEndian::read_u64(buf);
            self.set_mem(adr as u64, val);
        }
    }

    // Prepares arguments on the stack like a UNIX system. Note that we
    // pass an empty environment and that all strings will be properly
    // zero-terminated and word-aligned:
    //
    // | argc | argv[0] | ... | argv[n] | 0 | env[0] | ... | env[m] | 0 |
    //
    fn load_stack_segment(&mut self, argv: &[String]) {
        let argc = argv.len() as EmulatorValue;
        debug!("argc: {}, argv: {:?}", argc, argv);
        let argv_ptrs: Vec<EmulatorValue> = argv
            .iter()
            .rev()
            .map(|arg| {
                let c_string = arg.to_owned() + "\0\0\0\0\0\0\0\0";
                for chunk in c_string.as_bytes().chunks_exact(size_of::<u64>()).rev() {
                    self.push_stack(LittleEndian::read_u64(chunk));
                }
                self.get_reg(Register::Sp)
            })
            .collect();
        self.push_stack(0); // terminate env table
        self.push_stack(0); // terminate argv table
        for argv_ptr in argv_ptrs {
            self.push_stack(argv_ptr);
        }
        self.push_stack(argc);
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
    let address = state.program_counter & !WORD_SIZE_MASK;
    let offset = state.program_counter & WORD_SIZE_MASK;
    let bytes = state.get_mem(address).to_le_bytes();
    LittleEndian::read_u32(&bytes[(offset as usize)..])
}

fn decode(instruction_half_word: u32) -> Instruction {
    riscu::decode(instruction_half_word).expect("valid instruction")
}

fn execute(state: &mut EmulatorState, instr: Instruction) {
    match instr {
        Instruction::Lui(utype) => exec_lui(state, utype),
        Instruction::Jal(jtype) => exec_jal(state, jtype),
        Instruction::Jalr(itype) => exec_jalr(state, itype),
        Instruction::Beq(btype) => exec_beq(state, btype),
        Instruction::Ld(itype) => exec_ld(state, itype),
        Instruction::Sd(stype) => exec_sd(state, stype),
        Instruction::Addi(itype) => exec_addi(state, itype),
        Instruction::Add(rtype) => exec_add(state, rtype),
        Instruction::Sub(rtype) => exec_sub(state, rtype),
        Instruction::Sltu(rtype) => exec_sltu(state, rtype),
        Instruction::Mul(rtype) => exec_mul(state, rtype),
        Instruction::Divu(rtype) => exec_divu(state, rtype),
        Instruction::Remu(rtype) => exec_remu(state, rtype),
        Instruction::Ecall(_itype) => exec_ecall(state),
    }
}

fn exec_lui(state: &mut EmulatorState, utype: UType) {
    let rd_value = ((utype.imm() as i32) << 12) as u64;
    trace_utype(state, "lui", utype, rd_value);
    state.set_reg(utype.rd(), rd_value);
    state.pc_next();
}

fn exec_jal(state: &mut EmulatorState, jtype: JType) {
    let rd_value = state.program_counter + riscu::INSTRUCTION_SIZE as u64;
    trace_jtype(state, "jal", jtype, rd_value);
    state.set_reg_maybe(jtype.rd(), rd_value);
    state.pc_add(jtype.imm() as u64);
}

fn exec_jalr(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = state.program_counter + riscu::INSTRUCTION_SIZE as u64;
    let pc_value = rs1_value.wrapping_add(itype.imm() as u64);
    trace_itype(state, "jalr", itype, rd_value);
    state.set_reg_maybe(itype.rd(), rd_value);
    state.pc_set(pc_value);
}

fn exec_beq(state: &mut EmulatorState, btype: BType) {
    let rs1_value = state.get_reg(btype.rs1());
    let rs2_value = state.get_reg(btype.rs2());
    trace_btype(state, "beq", btype);
    if rs1_value == rs2_value {
        state.pc_add(btype.imm() as u64);
    } else {
        state.pc_next();
    }
}

fn exec_ld(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let address = rs1_value.wrapping_add(itype.imm() as u64);
    let rd_value = state.get_mem(address);
    trace_itype(state, "ld", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

fn exec_sd(state: &mut EmulatorState, stype: SType) {
    let rs1_value = state.get_reg(stype.rs1());
    let rs2_value = state.get_reg(stype.rs2());
    let address = rs1_value.wrapping_add(stype.imm() as u64);
    trace_stype(state, "sd", stype, address);
    state.set_mem(address, rs2_value);
    state.pc_next();
}

fn exec_addi(state: &mut EmulatorState, itype: IType) {
    let rs1_value = state.get_reg(itype.rs1());
    let rd_value = rs1_value.wrapping_add(itype.imm() as u64);
    trace_itype(state, "addi", itype, rd_value);
    state.set_reg(itype.rd(), rd_value);
    state.pc_next();
}

fn exec_add(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_add(rs2_value);
    trace_rtype(state, "add", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

fn exec_sub(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_sub(rs2_value);
    trace_rtype(state, "sub", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

fn exec_sltu(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = if rs1_value < rs2_value { 1 } else { 0 };
    trace_rtype(state, "sltu", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

fn exec_mul(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    let rd_value = rs1_value.wrapping_mul(rs2_value);
    trace_rtype(state, "mul", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

fn exec_divu(state: &mut EmulatorState, rtype: RType) {
    let rs1_value = state.get_reg(rtype.rs1());
    let rs2_value = state.get_reg(rtype.rs2());
    assert!(rs2_value != 0, "check for non-zero divisor");
    let rd_value = rs1_value.wrapping_div(rs2_value);
    trace_rtype(state, "divu", rtype, rd_value);
    state.set_reg(rtype.rd(), rd_value);
    state.pc_next();
}

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
        info!("program exiting with exit code {}", exit_code);
        state.running = false;
    } else if a7_value == SyscallId::Read as u64 {
        syscall_read(state);
    } else if a7_value == SyscallId::Write as u64 {
        syscall_write(state);
    } else if a7_value == SyscallId::Openat as u64 {
        syscall_openat(state);
    } else if a7_value == SyscallId::Brk as u64 {
        syscall_brk(state);
    } else {
        unimplemented!("unknown system call: {}", a7_value);
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

fn trace_btype(state: &EmulatorState, mne: &str, btype: BType) {
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
        state.get_reg(btype.rs1()) == state.get_reg(btype.rs2())
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
        "pc={:#x}: {} {:?},{}({:?}): {:?}={:#x}, {:?}={:#x} |- mem[{:#x}]={:#x} -> mem[{:#x}]={:#x}",
        state.program_counter,
        mne,
        stype.rs2(),
        stype.imm(),
        stype.rs1(),
        stype.rs1(),
        state.get_reg(stype.rs1()),
        stype.rs2(),
        state.get_reg(stype.rs2()),
        address,
        state.get_mem_maybe(address).unwrap_or(0),
        address,
        state.get_reg(stype.rs2())
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

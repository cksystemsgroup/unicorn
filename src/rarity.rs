use crate::{
    bug::Bug as BugDef,
    engine::{instruction_to_str, SyscallId},
};
use byteorder::{ByteOrder, LittleEndian};
use bytesize::ByteSize;
use itertools::Itertools;
use log::{debug, info, trace, warn};
use riscu::{
    decode, load_object_file, types::*, DecodingError, Instruction, Program, ProgramSegment,
    Register, RiscuError, INSTRUCTION_SIZE as INSTR_SIZE,
};
use std::{
    cmp::{min, Reverse},
    collections::HashMap,
    fmt,
    fs::{create_dir_all, File},
    io::Write,
    mem::size_of,
    path::Path,
    sync::Arc,
};
use thiserror::Error;

pub type Bug = BugDef<RarityBugInfo>;

const INSTRUCTION_SIZE: u64 = INSTR_SIZE as u64;

#[derive(Debug, Clone)]
pub struct State {
    pc: u64,
    regs: [Value; 32],
    #[allow(dead_code)]
    memory: Vec<Value>,
}

type Address = u64;
type Counter = u64;

fn compute_byte_value_rarity(states: &[&State]) -> HashMap<Address, Counter> {
    let mut scores = HashMap::new();

    fn count_score(scores: &mut HashMap<Address, Counter>, addr: Address) {
        if let Some(entry) = scores.get_mut(&addr) {
            *entry += 1;
        } else {
            scores.insert(addr, 1);
        }
    }

    for state in states {
        scorable_values(state, |it| it.for_each(|v| count_score(&mut scores, v)));
    }

    scores
}

fn scorable_values<F, R>(state: &State, mut f: F) -> R
where
    F: FnMut(&mut dyn Iterator<Item = u64>) -> R,
{
    let bytes_per_word = size_of::<u64>() as u64;
    let number_of_byte_values = 256;

    let pc_bytes = u64::to_ne_bytes(state.pc);

    let pc = pc_bytes
        .iter()
        .enumerate()
        .map(|(i, b)| i as u64 * number_of_byte_values + *b as u64);

    let offset = bytes_per_word * number_of_byte_values;

    let regs = state
        .regs
        .iter()
        .filter_map(|v| match v {
            Value::Concrete(w) => Some(w),
            _ => None,
        })
        .flat_map(|w| u64::to_ne_bytes(*w).iter().cloned().collect_vec())
        .enumerate()
        .map(|(i, b)| offset + i as u64 * number_of_byte_values + b as u64);

    let offset = 33 * bytes_per_word * number_of_byte_values;

    let memory = state
        .memory
        .iter()
        .filter_map(|v| match v {
            Value::Concrete(w) => Some(w),
            _ => None,
        })
        .flat_map(|w| u64::to_ne_bytes(*w).iter().cloned().collect_vec())
        .enumerate()
        .map(|(i, b)| offset + i as u64 * number_of_byte_values + b as u64);

    let mut iter = pc.chain(regs).chain(memory);

    f(&mut iter)
}

fn score_states(states: &[&State]) -> Vec<u64> {
    let rarity = compute_byte_value_rarity(states);

    let mut scores = Vec::new();

    for state in states {
        scorable_values(state, |it| {
            let score = it.map(|v| rarity.get(&v).unwrap()).sum();
            scores.push(score);
        });
    }

    scores
}

impl State {
    #[allow(dead_code)]
    fn write_to_file<P>(&self, path: P) -> Result<(), EngineError>
    where
        P: AsRef<Path>,
    {
        File::create(path)
            .and_then(|mut file| write!(file, "{}", self))
            .map_err(|e| EngineError::IoError(Arc::new(e)))
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "PC: 0x{:x}", self.pc)?;
        writeln!(f, "Register:")?;
        for (idx, val) in self.regs.iter().enumerate() {
            writeln!(f, "{:x}: {:?}", idx, val)?;
        }

        /*
        writeln!(f, "Memory:")?;
        for (idx, val) in self.memory.iter().enumerate() {
            writeln!(f, "{:#016x}: {:?}", idx, val)?;
        }
        */
        Ok(())
    }
}

pub fn execute<P>(
    input: P,
    output_dir: P,
    memory_size: ByteSize,
    number_of_states: u64,
    selection: u64,
    cycles: u64,
    iterations: u64,
) -> Result<Option<Bug>, EngineError>
where
    P: AsRef<Path>,
{
    let program = load_object_file(input).map_err(|e| EngineError::RiscuError(Arc::new(e)))?;

    create_and_run(
        &program,
        output_dir,
        memory_size,
        number_of_states,
        selection,
        cycles,
        iterations,
    )
}

fn create_and_run<P>(
    program: &Program,
    output_dir: P,
    memory_size: ByteSize,
    number_of_states: u64,
    selection: u64,
    cycles: u64,
    iterations: u64,
) -> Result<Option<Bug>, EngineError>
where
    P: AsRef<Path>,
{
    if !output_dir.as_ref().is_dir() {
        create_dir_all(&output_dir).map_err(|e| EngineError::IoError(Arc::new(e)))?;
    }

    let mut engines: Vec<Engine> = Vec::new();

    for iteration in 0..iterations {
        info!("Running rarity simulation round {}...", iteration + 1);

        let to_create = number_of_states as usize - engines.len();
        info!("Creating {} new states", to_create);
        engines.extend((0..to_create).map(|_| Engine::new(&program, memory_size)));

        let results = time_info!("Running engines", {
            let results: Vec<_> = engines
                .iter_mut()
                .map(|engine| engine.run(cycles))
                .collect();

            if let Some(error_or_bug) = results.clone().iter().find(|result| match result {
                Err(EngineError::ExecutionDepthReached(_)) => false,
                Err(_) | Ok(Some(_)) => true,
                _ => false,
            }) {
                return error_or_bug.clone();
            }

            results
        });

        // remove successfully exited engines
        engines = engines
            .iter()
            .cloned()
            .zip(results)
            .filter(|(_, r)| matches!(r, Err(EngineError::ExecutionDepthReached(_))))
            .map(|(e, _)| e)
            .collect();

        info!(
            "Remove {} successfully exited states from selection",
            number_of_states as usize - engines.len()
        );

        let scores = time_info!("Scoring states", {
            let states: Vec<_> = engines.iter().map(|e| e.state()).collect();

            score_states(states.as_slice())
        });

        info!("  scored states: {:?}", scores);

        let selection = min(selection as usize, engines.len());

        engines = engines
            .iter()
            .zip(scores)
            .sorted_by_key(|x| Reverse(x.1))
            .map(|x| (*x.0).clone())
            .take(selection)
            .collect();

        info!("  selecting {} states", selection);
    }

    Ok(None)
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Value {
    Concrete(u64),
    Uninitialized,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Concrete(c) => write!(f, "{:#x}", c),
            Value::Uninitialized => write!(f, "uninit"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Engine {
    program_break: u64,
    state: State,
    execution_depth: u64,
    max_exection_depth: u64,
    concrete_inputs: Vec<u64>,
    is_running: bool,
}

impl Engine {
    // creates a machine state with a specific memory size
    pub fn new(program: &Program, memory_size: ByteSize) -> Self {
        assert!(
            memory_size.as_u64() % 8 == 0,
            "memory size has to be a multiple of 8"
        );

        let mut regs = [Value::Uninitialized; 32];
        let mut memory = vec![Value::Uninitialized; memory_size.as_u64() as usize / 8];

        let sp = memory_size.as_u64() - 8;
        regs[Register::Sp as usize] = Value::Concrete(sp);
        regs[Register::Zero as usize] = Value::Concrete(0);

        // TODO: Init main function arguments
        let argc = 0;
        memory[sp as usize / size_of::<u64>()] = Value::Concrete(argc);

        load_segment(&mut memory, &program.code);
        load_segment(&mut memory, &program.data);

        let pc = program.code.address;

        let program_break = program.data.address + program.data.content.len() as u64;

        debug!(
            "initializing new execution context with {} of main memory",
            memory_size
        );
        debug!(
            "code segment: start={:#x} length={}",
            program.code.address,
            program.code.content.len(),
        );
        debug!(
            "data segment: start={:#x} length={}",
            program.data.address,
            program.data.content.len(),
        );
        debug!(
            "init state: pc={:#x} brk={:#x}, argc={}",
            pc, program_break, argc
        );

        Self {
            program_break,
            state: State { pc, regs, memory },
            execution_depth: 0,
            max_exection_depth: 0,
            concrete_inputs: Vec::new(),
            is_running: false,
        }
    }

    pub fn state(&self) -> &State {
        &self.state
    }

    pub fn run(&mut self, number_of_instructions: u64) -> Result<Option<Bug>, EngineError> {
        self.is_running = true;
        self.max_exection_depth += number_of_instructions;

        loop {
            if self.execution_depth >= self.max_exection_depth {
                trace!("maximum execution depth reached => exiting this context");

                self.is_running = false;

                return Err(EngineError::ExecutionDepthReached(self.execution_depth));
            }

            self.execution_depth += 1;

            let bug = self
                .fetch()
                .and_then(|raw| self.decode(raw))
                .and_then(|instr| self.execute(instr))?;

            if bug.is_some() || !self.is_running {
                return Ok(bug);
            }
        }
    }

    fn fetch(&self) -> Result<u32, EngineError> {
        if let Value::Concrete(dword) =
            self.state.memory[(self.state.pc as usize / size_of::<u64>()) as usize]
        {
            if self.state.pc % size_of::<u64>() as u64 == 0 {
                Ok(dword as u32)
            } else {
                Ok((dword >> 32) as u32)
            }
        } else {
            Err(EngineError::NotSupported(String::from(
                "tried to fetch none concrete instruction",
            )))
        }
    }

    fn decode(&self, raw: u32) -> Result<Instruction, EngineError> {
        decode(raw).map_err(|e| EngineError::InvalidInstructionEncoding(self.state.pc, e))
    }

    fn execute(&mut self, instruction: Instruction) -> Result<Option<Bug>, EngineError> {
        match instruction {
            Instruction::Ecall(_) => self.execute_ecall(),
            Instruction::Lui(utype) => self.execute_lui(utype),
            Instruction::Addi(itype) => self.execute_itype(instruction, itype, u64::wrapping_add),
            Instruction::Add(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_add),
            Instruction::Sub(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_sub),
            Instruction::Mul(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_mul),
            Instruction::Divu(rtype) => self.execute_divu(instruction, rtype),
            Instruction::Remu(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_rem),
            Instruction::Sltu(rtype) => {
                self.execute_rtype(instruction, rtype, |l, r| if l < r { 1 } else { 0 })
            }
            Instruction::Ld(itype) => self.execute_ld(instruction, itype),
            Instruction::Sd(stype) => self.execute_sd(instruction, stype),
            Instruction::Jal(jtype) => self.execute_jal(jtype),
            Instruction::Jalr(itype) => self.execute_jalr(itype),
            Instruction::Beq(btype) => self.execute_beq(btype),
        }
    }

    fn check_for_uninitialized_memory(
        &mut self,
        instruction: Instruction,
        v1: Value,
        v2: Value,
    ) -> Result<Option<Bug>, EngineError> {
        trace!(
            "{}: {}, {} => computing reachability",
            instruction_to_str(instruction),
            v1,
            v2
        );

        Ok(Some(Bug::AccessToUnitializedMemory {
            info: RarityBugInfo {
                witness: self.concrete_inputs.clone(),
                pc: self.state.pc,
            },
            instruction,
            // TODO: fix operands
            operands: vec![],
        }))
    }

    fn is_in_vaddr_range(&self, vaddr: u64) -> bool {
        vaddr as usize / size_of::<u64>() < self.state.memory.len()
    }

    fn check_for_valid_memory_address(
        &mut self,
        instruction: &str,
        address: u64,
    ) -> Result<Option<Bug>, EngineError> {
        let is_alignment_ok = address % size_of::<u64>() as u64 == 0;

        if !is_alignment_ok {
            trace!(
                "{}: address {:#x} is not double word aligned => computing reachability",
                instruction,
                address
            );

            self.is_running = false;

            Ok(Some(Bug::AccessToUnalignedAddress {
                info: RarityBugInfo {
                    witness: self.concrete_inputs.clone(),
                    pc: self.state.pc,
                },
                address,
            }))
        } else if !self.is_in_vaddr_range(address) {
            trace!(
                "{}: address {:#x} out of virtual address range (0x0 - {:#x}) => computing reachability",
                instruction,
                address,
                self.state.memory.len() * 8,
            );

            self.is_running = false;

            Ok(Some(Bug::AccessToOutOfRangeAddress {
                info: RarityBugInfo {
                    witness: self.concrete_inputs.clone(),
                    pc: self.state.pc,
                },
            }))
        } else {
            Ok(None)
        }
    }

    fn execute_lui(&mut self, utype: UType) -> Result<Option<Bug>, EngineError> {
        let immediate = u64::from(utype.imm()) << 12;

        let result = Value::Concrete(immediate);

        trace!(
            "[{:#010x}] {}: {:?} <- {}",
            self.state.pc,
            instruction_to_str(Instruction::Lui(utype)),
            utype.rd(),
            result,
        );

        self.assign_rd(utype.rd(), result);

        self.state.pc += INSTRUCTION_SIZE;

        Ok(None)
    }

    fn execute_divu(
        &mut self,
        instruction: Instruction,
        rtype: RType,
    ) -> Result<Option<Bug>, EngineError> {
        match self.state.regs[rtype.rs2() as usize] {
            Value::Concrete(divisor) if divisor == 0 => {
                trace!("divu: divisor == 0 -> compute reachability");

                Ok(Some(Bug::DivisionByZero {
                    info: RarityBugInfo {
                        witness: self.concrete_inputs.clone(),
                        pc: self.state.pc,
                    },
                }))
            }
            _ => self.execute_rtype(instruction, rtype, u64::wrapping_div),
        }
    }

    fn execute_itype<Op>(
        &mut self,
        instruction: Instruction,
        itype: IType,
        op: Op,
    ) -> Result<Option<Bug>, EngineError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let rs1_value = self.state.regs[itype.rs1() as usize];
        let imm_value = Value::Concrete(itype.imm() as u64);

        self.execute_binary_op(instruction, rs1_value, imm_value, itype.rd(), op)
    }

    fn execute_rtype<Op>(
        &mut self,
        instruction: Instruction,
        rtype: RType,
        op: Op,
    ) -> Result<Option<Bug>, EngineError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let rs1_value = self.state.regs[rtype.rs1() as usize];
        let rs2_value = self.state.regs[rtype.rs2() as usize];

        self.execute_binary_op(instruction, rs1_value, rs2_value, rtype.rd(), op)
    }

    fn execute_binary_op<Op>(
        &mut self,
        instruction: Instruction,
        lhs: Value,
        rhs: Value,
        rd: Register,
        op: Op,
    ) -> Result<Option<Bug>, EngineError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let result = match (lhs, rhs) {
            (Value::Concrete(v1), Value::Concrete(v2)) => Value::Concrete(op(v1, v2)),
            _ => {
                let bug = self.check_for_uninitialized_memory(instruction, lhs, rhs)?;

                trace!("could not find input assignment => exeting this context");

                self.is_running = false;

                return Ok(bug);
            }
        };

        trace!(
            "[{:#010x}] {}:  {}, {} |- {:?} <- {}",
            self.state.pc,
            instruction_to_str(instruction),
            lhs,
            rhs,
            rd,
            result,
        );

        self.assign_rd(rd, result);

        self.state.pc += INSTRUCTION_SIZE;

        Ok(None)
    }

    fn execute_brk(&mut self) -> Result<Option<Bug>, EngineError> {
        if let Value::Concrete(new_program_break) = self.state.regs[Register::A0 as usize] {
            let old_program_break = self.program_break;

            if new_program_break < self.program_break || !self.is_in_vaddr_range(new_program_break)
            {
                self.state.regs[Register::A0 as usize] = Value::Concrete(self.program_break);
            } else {
                self.program_break = new_program_break;
            }

            trace!(
                "brk: old={:#x} new={:#x}",
                old_program_break,
                new_program_break
            );

            Ok(None)
        } else {
            not_supported("can not handle symbolic or uninitialized program break")
        }
    }

    fn execute_read(&mut self) -> Result<Option<Bug>, EngineError> {
        if !matches!(self.state.regs[Register::A0 as usize], Value::Concrete(0)) {
            return not_supported("can not handle other fd than stdin in read syscall");
        }

        let buffer = if let Value::Concrete(b) = self.state.regs[Register::A1 as usize] {
            b
        } else {
            return not_supported(
                "can not handle symbolic or uninitialized buffer address in read syscall",
            );
        };

        let size = if let Value::Concrete(s) = self.state.regs[Register::A2 as usize] {
            s
        } else {
            return not_supported("can not handle symbolic or uinitialized size in read syscall");
        };

        trace!("read: fd={} buffer={:#x} size={}", 0, buffer, size,);

        if !self.is_in_vaddr_range(buffer) || !self.is_in_vaddr_range(buffer + size) {
            return not_supported("read syscall failed to");
        }

        let size_of_u64 = size_of::<u64>() as u64;

        let round_up = if size % size_of_u64 == 0 {
            0
        } else {
            size_of_u64 - size % size_of_u64
        };

        let mut bytes_to_read = size;
        let words_to_read = (bytes_to_read + round_up) / size_of_u64;

        let start = buffer / size_of_u64;

        for word_count in 0..words_to_read {
            let result = if bytes_to_read >= size_of_u64 {
                bytes_to_read -= size_of_u64;

                let new = rand::random();

                self.concrete_inputs.push(new);

                new
            } else if let Value::Concrete(c) = self.state.memory[(start + word_count) as usize] {
                let bits_in_a_byte = 8;

                let low_shift_factor = 2_u64.pow(bytes_to_read as u32 * bits_in_a_byte);

                let high_shift_factor =
                    2_u64.pow((size_of::<u64>() as u32 - bytes_to_read as u32) * bits_in_a_byte);

                let prev = c / low_shift_factor * low_shift_factor;
                let new = rand::random::<u64>().wrapping_mul(high_shift_factor) / high_shift_factor;

                self.concrete_inputs.push(new);

                prev + new
            } else {
                // we do not partially overwrite words with concrete values
                // if at least one byte in a word is uninitialized, the whole word is uninitialized

                warn!(
                    "read: Ignoring partial read on uninitialized word at {:#016x}",
                    start + word_count
                );

                break;
            };

            self.state.memory[(start + word_count) as usize] = Value::Concrete(result);
        }

        self.state.regs[Register::A0 as usize] = Value::Concrete(size);

        Ok(None)
    }

    fn execute_beq(&mut self, btype: BType) -> Result<Option<Bug>, EngineError> {
        let lhs = self.state.regs[btype.rs1() as usize];
        let rhs = self.state.regs[btype.rs2() as usize];

        let true_branch = self.state.pc.wrapping_add(btype.imm() as u64);
        let false_branch = self.state.pc.wrapping_add(INSTRUCTION_SIZE as u64);

        match (lhs, rhs) {
            (Value::Concrete(v1), Value::Concrete(v2)) => {
                let old_pc = self.state.pc;

                self.state.pc = if v1 == v2 { true_branch } else { false_branch };

                trace!(
                    "[{:#010x}] beq: {}, {} |- pc <- {:#x}",
                    old_pc,
                    lhs,
                    rhs,
                    self.state.pc
                );

                Ok(None)
            }
            (v1, v2) => {
                self.is_running = false;

                let result = self.check_for_uninitialized_memory(Instruction::Beq(btype), v1, v2);

                trace!("access to uninitialized memory => exeting this context");

                result
            }
        }
    }

    fn execute_exit(&mut self) -> Result<Option<Bug>, EngineError> {
        self.is_running = false;

        match self.state.regs[Register::A0 as usize] {
            Value::Concrete(exit_code) => {
                if exit_code > 0 {
                    trace!(
                        "exit: with code {} -> find input to satisfy path condition",
                        exit_code
                    );

                    Ok(Some(Bug::ExitCodeGreaterZero {
                        info: RarityBugInfo {
                            witness: self.concrete_inputs.clone(),
                            pc: self.state.pc,
                        },
                    }))
                } else {
                    trace!("exiting context with exit_code 0");

                    Ok(None)
                }
            }
            _ => not_supported("exit only implemented for symbolic exit codes"),
        }
    }

    fn execute_ecall(&mut self) -> Result<Option<Bug>, EngineError> {
        trace!("[{:#010x}] ecall", self.state.pc);

        let result = match self.state.regs[Register::A7 as usize] {
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Brk as u64) => {
                self.execute_brk()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Read as u64) => {
                self.execute_read()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Exit as u64) => {
                self.execute_exit()
            }
            id => Err(EngineError::NotSupported(format!(
                "syscall with id ({}) is not supported",
                id
            ))),
        };

        self.state.pc += INSTRUCTION_SIZE;

        result
    }

    fn execute_ld(
        &mut self,
        instruction: Instruction,
        itype: IType,
    ) -> Result<Option<Bug>, EngineError> {
        if let Value::Concrete(base_address) = self.state.regs[itype.rs1() as usize] {
            let immediate = itype.imm() as u64;

            let address = base_address.wrapping_add(immediate);

            let bug =
                self.check_for_valid_memory_address(instruction_to_str(instruction), address)?;

            if bug.is_none() {
                let value = self.state.memory[(address / 8) as usize];

                trace!(
                    "[{:#010x}] {}: {:#x}, {} |- {:?} <- mem[{:#x}]={}",
                    self.state.pc,
                    instruction_to_str(instruction),
                    base_address,
                    immediate,
                    itype.rd(),
                    address,
                    value,
                );

                self.assign_rd(itype.rd(), value);

                self.state.pc += INSTRUCTION_SIZE;
            }

            Ok(bug)
        } else {
            not_supported("can not handle symbolic addresses in LD")
        }
    }

    fn execute_sd(
        &mut self,
        instruction: Instruction,
        stype: SType,
    ) -> Result<Option<Bug>, EngineError> {
        if let Value::Concrete(base_address) = self.state.regs[stype.rs1() as usize] {
            let immediate = stype.imm();

            let address = base_address.wrapping_add(immediate as u64);

            let bug =
                self.check_for_valid_memory_address(instruction_to_str(instruction), address)?;

            if bug.is_none() {
                let value = self.state.regs[stype.rs2() as usize];

                trace!(
                    "[{:#010x}] {}: {:#x}, {}, {} |- mem[{:#x}] <- {}",
                    self.state.pc,
                    instruction_to_str(instruction),
                    base_address,
                    immediate,
                    self.state.regs[stype.rs2() as usize],
                    address,
                    value,
                );

                self.state.memory[(address / 8) as usize] = value;

                self.state.pc += INSTRUCTION_SIZE;
            }

            Ok(bug)
        } else {
            not_supported("can not handle uninitialized addresses in SD")
        }
    }

    fn execute_jal(&mut self, jtype: JType) -> Result<Option<Bug>, EngineError> {
        let link = self.state.pc + INSTRUCTION_SIZE;

        let new_pc = self.state.pc.wrapping_add(jtype.imm() as u64);

        trace!(
            "[{:#010x}] jal: pc <- {:#x}, {:?} <- {:#x}",
            self.state.pc,
            new_pc,
            jtype.rd(),
            link,
        );

        self.state.pc = new_pc;

        self.assign_rd(jtype.rd(), Value::Concrete(link));

        Ok(None)
    }

    fn assign_rd(&mut self, rd: Register, v: Value) {
        if rd != Register::Zero {
            self.state.regs[rd as usize] = v;
        }
    }

    fn execute_jalr(&mut self, itype: IType) -> Result<Option<Bug>, EngineError> {
        if let Value::Concrete(dest) = self.state.regs[itype.rs1() as usize] {
            let link = self.state.pc + INSTRUCTION_SIZE;

            let new_pc = dest.wrapping_add(itype.imm() as u64);

            trace!(
                "[{:#010x}] jalr: {:#x}, {} |- pc <- {:#x}, {:?} <- {:#x}",
                self.state.pc,
                dest,
                itype.imm(),
                new_pc,
                itype.rd(),
                link
            );

            self.assign_rd(itype.rd(), Value::Concrete(link));

            self.state.pc = new_pc;

            Ok(None)
        } else {
            not_supported("can only handle concrete addresses in JALR")
        }
    }
}

#[derive(Debug, Clone, Error)]
pub enum EngineError {
    #[error("failed to load RISC-U binary")]
    RiscuError(Arc<RiscuError>),

    #[error("failed to write State to file")]
    IoError(Arc<std::io::Error>),

    #[error("engine does not support {0}")]
    NotSupported(String),

    #[error("failed to decode instruction at PC: {0:#010x}")]
    InvalidInstructionEncoding(u64, DecodingError),

    #[error("has reached the maximum execution depth of {0}")]
    ExecutionDepthReached(u64),
}

fn load_segment(memory: &mut Vec<Value>, segment: &ProgramSegment<u8>) {
    let start = segment.address as usize / size_of::<u64>();
    let end = start + segment.content.len() / size_of::<u64>();

    segment
        .content
        .chunks(size_of::<u64>())
        .map(LittleEndian::read_u64)
        .zip(start..end)
        .for_each(|(x, i)| memory[i] = Value::Concrete(x));
}

fn not_supported(s: &str) -> Result<Option<Bug>, EngineError> {
    Err(EngineError::NotSupported(s.to_owned()))
}

#[derive(Default, Debug, Clone)]
pub struct RarityBugInfo {
    witness: Vec<u64>,
    pc: u64,
}

impl fmt::Display for RarityBugInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "concrete inputs read: {:?}", self.witness)?;
        writeln!(f, "pc: {:#x}", self.pc)
    }
}

use crate::{
    boolector::Boolector,
    bug::{BasicInfo, Bug},
    cfg::build_cfg_from_file,
    exploration_strategy::{ExplorationStrategy, ShortestPathStrategy},
    solver::{MonsterSolver, Solver, SolverError},
    symbolic_state::{BVOperator, Query, SymbolId, SymbolicState},
    z3::Z3,
};
use byteorder::{ByteOrder, LittleEndian};
use bytesize::ByteSize;
use log::{debug, trace};
use riscu::{
    decode, types::*, DecodingError, Instruction, Program, ProgramSegment, Register,
    INSTRUCTION_SIZE as INSTR_SIZE,
};
use std::{fmt, mem::size_of, path::Path, rc::Rc};
use thiserror::Error;

const INSTRUCTION_SIZE: u64 = INSTR_SIZE as u64;

#[allow(dead_code)]
pub enum SyscallId {
    Exit = 93,
    Read = 63,
    Write = 64,
    Openat = 56,
    Brk = 214,
}
#[derive(Clone, Copy)]
pub enum Backend {
    Monster,
    Boolector,
    Z3,
}

pub fn execute<P>(
    input: P,
    with: Backend,
    max_exection_depth: u64,
    memory_size: ByteSize,
) -> Result<Option<Bug>, EngineError>
where
    P: AsRef<Path>,
{
    let ((graph, _), program) = build_cfg_from_file(input).map_err(EngineError::IoError)?;

    let strategy = ShortestPathStrategy::new(&graph, program.code.address);

    match with {
        Backend::Monster => {
            create_and_run::<_, MonsterSolver>(&program, &strategy, max_exection_depth, memory_size)
        }
        Backend::Boolector => {
            create_and_run::<_, Boolector>(&program, &strategy, max_exection_depth, memory_size)
        }
        Backend::Z3 => {
            create_and_run::<_, Z3>(&program, &strategy, max_exection_depth, memory_size)
        }
    }
}

fn create_and_run<E, S>(
    program: &Program,
    strategy: &E,
    max_exection_depth: u64,
    memory_size: ByteSize,
) -> Result<Option<Bug>, EngineError>
where
    E: ExplorationStrategy,
    S: Solver + Default,
{
    let solver = Rc::new(S::default());
    let state = Box::new(SymbolicState::new(solver));

    Engine::new(memory_size, max_exection_depth, &program, strategy, state).run()
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Value {
    Concrete(u64),
    Symbolic(SymbolId),
    Uninitialized,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Concrete(c) => write!(f, "{:#x}", c),
            Value::Symbolic(i) => write!(f, "x{}", i.index()),
            Value::Uninitialized => write!(f, "uninit"),
        }
    }
}

#[derive(Debug, Error)]
pub enum EngineError {
    #[error("failed to load binary")]
    IoError(anyhow::Error),

    #[error("engine does not support {0}")]
    NotSupported(String),

    #[error("has reached the maximum execution depth of {0}")]
    ExecutionDepthReached(u64),

    #[error("failed to decode instruction at PC: {0:#010x}")]
    InvalidInstructionEncoding(u64, DecodingError),

    #[error("failed to compute satisfyability for formula")]
    SatUnknown(SolverError),
}

pub struct Engine<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    symbolic_state: Box<SymbolicState<S>>,
    program_break: u64,
    pc: u64,
    regs: [Value; 32],
    memory: Vec<Value>,
    strategy: &'a E,
    execution_depth: u64,
    max_exection_depth: u64,
    is_running: bool,
}

impl<'a, E, S> Engine<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    // creates a machine state with a specific memory size
    pub fn new(
        memory_size: ByteSize,
        max_exection_depth: u64,
        program: &Program,
        strategy: &'a E,
        symbolic_state: Box<SymbolicState<S>>,
    ) -> Self {
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
            symbolic_state,
            program_break,
            pc,
            regs,
            memory,
            strategy,
            execution_depth: 0,
            max_exection_depth,
            is_running: false,
        }
    }

    fn decode(&self, raw: u32) -> Result<Instruction, EngineError> {
        decode(raw).map_err(|e| EngineError::InvalidInstructionEncoding(self.pc, e))
    }

    pub fn run(&mut self) -> Result<Option<Bug>, EngineError> {
        self.is_running = true;

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

    fn execute_query<F>(
        &mut self,
        query: Query,
        basic_info_to_bug: F,
    ) -> Result<Option<Bug>, EngineError>
    where
        F: Fn(BasicInfo) -> Bug,
    {
        Ok(self
            .symbolic_state
            .execute_query(query)
            .map_err(EngineError::SatUnknown)
            .map_or(None, |result| {
                result.map(|witness| {
                    basic_info_to_bug(BasicInfo {
                        witness,
                        pc: self.pc,
                    })
                })
            }))
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

        self.execute_query(Query::Reachable, |info| Bug::AccessToUnitializedMemory {
            info,
            instruction,
            operands: vec![v1, v2],
        })
    }

    fn is_in_vaddr_range(&self, vaddr: u64) -> bool {
        vaddr as usize / size_of::<u64>() < self.memory.len()
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

            self.execute_query(Query::Reachable, |info| Bug::AccessToUnalignedAddress {
                info,
                address,
            })
        } else if !self.is_in_vaddr_range(address) {
            trace!(
                "{}: address {:#x} out of virtual address range (0x0 - {:#x}) => computing reachability",
                instruction,
                address,
                self.memory.len() * 8,
            );

            self.is_running = false;

            self.execute_query(Query::Reachable, |info| Bug::AccessToOutOfRangeAddress {
                info,
            })
        } else {
            Ok(None)
        }
    }

    fn execute_lui(&mut self, utype: UType) -> Result<Option<Bug>, EngineError> {
        let immediate = u64::from(utype.imm()) << 12;

        let result = Value::Concrete(immediate);

        trace!(
            "[{:#010x}] {}: {:?} <- {}",
            self.pc,
            instruction_to_str(Instruction::Lui(utype)),
            utype.rd(),
            result,
        );

        self.assign_rd(utype.rd(), result);

        self.pc += INSTRUCTION_SIZE;

        Ok(None)
    }

    fn execute_divu(
        &mut self,
        instruction: Instruction,
        rtype: RType,
    ) -> Result<Option<Bug>, EngineError> {
        let bug = match self.regs[rtype.rs2() as usize] {
            Value::Symbolic(divisor) => {
                trace!("divu: symbolic divisor -> find input for divisor == 0");

                self.execute_query(Query::Equals((divisor, 0)), |info| Bug::DivisionByZero {
                    info,
                })?
            }
            Value::Concrete(divisor) if divisor == 0 => {
                trace!("divu: divisor == 0 -> compute reachability");

                self.execute_query(Query::Reachable, |info| Bug::DivisionByZero { info })?
            }
            _ => None,
        };

        if bug.is_none() {
            self.execute_rtype(instruction, rtype, u64::wrapping_div)
        } else {
            Ok(bug)
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
        let rs1_value = self.regs[itype.rs1() as usize];
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
        let rs1_value = self.regs[rtype.rs1() as usize];
        let rs2_value = self.regs[rtype.rs2() as usize];

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
            (Value::Symbolic(v1), Value::Concrete(v2)) => {
                let v2 = self.symbolic_state.create_const(v2);
                Value::Symbolic(self.symbolic_state.create_instruction(instruction, v1, v2))
            }
            (Value::Concrete(v1), Value::Symbolic(v2)) => {
                let v1 = self.symbolic_state.create_const(v1);
                Value::Symbolic(self.symbolic_state.create_instruction(instruction, v1, v2))
            }
            (Value::Symbolic(v1), Value::Symbolic(v2)) => {
                Value::Symbolic(self.symbolic_state.create_instruction(instruction, v1, v2))
            }
            _ => {
                let bug = self.check_for_uninitialized_memory(instruction, lhs, rhs)?;

                trace!("could not find input assignment => exeting this context");

                self.is_running = false;

                return Ok(bug);
            }
        };

        trace!(
            "[{:#010x}] {}:  {}, {} |- {:?} <- {}",
            self.pc,
            instruction_to_str(instruction),
            lhs,
            rhs,
            rd,
            result,
        );

        self.assign_rd(rd, result);

        self.pc += INSTRUCTION_SIZE;

        Ok(None)
    }

    fn execute_brk(&mut self) -> Result<Option<Bug>, EngineError> {
        if let Value::Concrete(new_program_break) = self.regs[Register::A0 as usize] {
            let old_program_break = self.program_break;

            if new_program_break < self.program_break || !self.is_in_vaddr_range(new_program_break)
            {
                self.regs[Register::A0 as usize] = Value::Concrete(self.program_break);
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

    fn bytewise_combine(&mut self, old: Value, n_lower_bytes: u32, new_idx: SymbolId) -> SymbolId {
        let bits_in_a_byte = 8;
        let low_shift_factor = 2_u64.pow(n_lower_bytes * bits_in_a_byte);
        let high_shift_factor =
            2_u64.pow((size_of::<u64>() as u32 - n_lower_bytes) * bits_in_a_byte);

        assert!(
            low_shift_factor != 0 && high_shift_factor != 0,
            "no bytes to shift"
        );

        let old_idx = match old {
            Value::Concrete(c) => {
                let old_c = c / low_shift_factor * low_shift_factor;

                self.symbolic_state.create_const(old_c)
            }
            Value::Symbolic(old_idx) => {
                let low_shift_factor_idx = self.symbolic_state.create_const(low_shift_factor);

                let old_idx = self.symbolic_state.create_operator(
                    BVOperator::Divu,
                    old_idx,
                    low_shift_factor_idx,
                );

                self.symbolic_state
                    .create_operator(BVOperator::Mul, old_idx, low_shift_factor_idx)
            }
            Value::Uninitialized => {
                unreachable!("function should not be called for uninitialized values")
            }
        };

        let high_shift_factor_idx = self.symbolic_state.create_const(high_shift_factor);

        let new_idx =
            self.symbolic_state
                .create_operator(BVOperator::Mul, new_idx, high_shift_factor_idx);

        let new_idx =
            self.symbolic_state
                .create_operator(BVOperator::Divu, new_idx, high_shift_factor_idx);

        self.symbolic_state
            .create_operator(BVOperator::Add, old_idx, new_idx)
    }

    fn execute_read(&mut self) -> Result<Option<Bug>, EngineError> {
        if !matches!(self.regs[Register::A0 as usize], Value::Concrete(0)) {
            return not_supported("can not handle other fd than stdin in read syscall");
        }

        let buffer = if let Value::Concrete(b) = self.regs[Register::A1 as usize] {
            b
        } else {
            return not_supported(
                "can not handle symbolic or uninitialized buffer address in read syscall",
            );
        };

        let size = if let Value::Concrete(s) = self.regs[Register::A2 as usize] {
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
            let start_byte = word_count * size_of_u64;
            let end_byte = start_byte
                + if bytes_to_read < size_of_u64 {
                    bytes_to_read
                } else {
                    8
                };

            let name = format!(
                "read({}, {}, {})[{} - {}]",
                0, buffer, size, start_byte, end_byte,
            );

            let input_idx = self.symbolic_state.create_input(&name);

            let result_idx = if bytes_to_read >= size_of_u64 {
                bytes_to_read -= size_of_u64;

                input_idx
            } else {
                match self.memory[(start + word_count) as usize] {
                    Value::Uninitialized => {
                        // we do not partially overwrite words with concrete values
                        // if at least one byte in a word is uninitialized, the whole word is uninitialized
                        break;
                    }
                    v => self.bytewise_combine(v, bytes_to_read as u32, input_idx),
                }
            };

            self.memory[(start + word_count) as usize] = Value::Symbolic(result_idx);
        }

        self.regs[Register::A0 as usize] = Value::Concrete(size);

        Ok(None)
    }

    fn execute_beq_branches(
        &mut self,
        true_branch: u64,
        false_branch: u64,
        lhs: SymbolId,
        rhs: SymbolId,
    ) -> Result<Option<Bug>, EngineError> {
        let memory_snapshot = self.memory.clone();
        let regs_snapshot = self.regs;
        let graph_snapshot = Box::new((*self.symbolic_state).clone());
        let brk_snapshot = self.program_break;
        let execution_depth_snapshot = self.execution_depth;

        let next_pc = self.strategy.choose_path(true_branch, false_branch);

        let decision = next_pc == true_branch;

        self.symbolic_state
            .create_beq_path_condition(decision, lhs, rhs);

        trace!(
            "[{:#010x}] beq: x{}, x{} |- assume {}, pc <- {:#x}",
            self.pc,
            lhs.index(),
            rhs.index(),
            next_pc == false_branch,
            next_pc,
        );

        self.pc = next_pc;

        let result = self.run();

        if !matches!(result, Err(EngineError::ExecutionDepthReached(_)) | Ok(None)) {
            return result;
        }

        self.is_running = true;

        self.memory = memory_snapshot;
        self.regs = regs_snapshot;
        self.symbolic_state = graph_snapshot;
        self.program_break = brk_snapshot;
        self.execution_depth = execution_depth_snapshot;

        let next_pc = if decision { false_branch } else { true_branch };

        self.symbolic_state
            .create_beq_path_condition(!decision, lhs, rhs);

        trace!(
            "[{:#010x}] beq: x{}, x{} |- assume {}, pc <- {:#x}",
            self.pc,
            lhs.index(),
            rhs.index(),
            next_pc == false_branch,
            next_pc,
        );

        self.pc = next_pc;

        Ok(None)
    }

    fn execute_beq(&mut self, btype: BType) -> Result<Option<Bug>, EngineError> {
        let lhs = self.regs[btype.rs1() as usize];
        let rhs = self.regs[btype.rs2() as usize];

        let true_branch = self.pc.wrapping_add(btype.imm() as u64);
        let false_branch = self.pc.wrapping_add(4);

        match (lhs, rhs) {
            (Value::Concrete(v1), Value::Concrete(v2)) => {
                let old_pc = self.pc;

                self.pc = if v1 == v2 { true_branch } else { false_branch };

                trace!(
                    "[{:#010x}] beq: {}, {} |- pc <- {:#x}",
                    old_pc,
                    lhs,
                    rhs,
                    self.pc
                );

                Ok(None)
            }
            (Value::Symbolic(v1), Value::Concrete(v2)) => {
                let v2 = self.symbolic_state.create_const(v2);
                self.execute_beq_branches(true_branch, false_branch, v1, v2)
            }
            (Value::Concrete(v1), Value::Symbolic(v2)) => {
                let v1 = self.symbolic_state.create_const(v1);
                self.execute_beq_branches(true_branch, false_branch, v1, v2)
            }
            (Value::Symbolic(v1), Value::Symbolic(v2)) => {
                self.execute_beq_branches(true_branch, false_branch, v1, v2)
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

        match self.regs[Register::A0 as usize] {
            Value::Symbolic(exit_code) => {
                trace!("exit: symbolic code -> find input for exit_code != 0");

                self.execute_query(Query::NotEquals((exit_code, 0)), |info| {
                    Bug::ExitCodeGreaterZero { info }
                })
            }
            Value::Concrete(exit_code) => {
                if exit_code > 0 {
                    trace!(
                        "exit: with code {} -> find input to satisfy path condition",
                        exit_code
                    );

                    self.execute_query(Query::Reachable, |info| Bug::ExitCodeGreaterZero { info })
                } else {
                    trace!("exiting context with exit_code 0");

                    Ok(None)
                }
            }
            _ => not_supported("exit only implemented for symbolic exit codes"),
        }
    }

    fn execute_ecall(&mut self) -> Result<Option<Bug>, EngineError> {
        trace!("[{:#010x}] ecall", self.pc);

        let result = match self.regs[Register::A7 as usize] {
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

        self.pc += INSTRUCTION_SIZE;

        result
    }

    fn execute_ld(
        &mut self,
        instruction: Instruction,
        itype: IType,
    ) -> Result<Option<Bug>, EngineError> {
        if let Value::Concrete(base_address) = self.regs[itype.rs1() as usize] {
            let immediate = itype.imm() as u64;

            let address = base_address.wrapping_add(immediate);

            let bug =
                self.check_for_valid_memory_address(instruction_to_str(instruction), address)?;

            if bug.is_none() {
                let value = self.memory[(address / 8) as usize];

                trace!(
                    "[{:#010x}] {}: {:#x}, {} |- {:?} <- mem[{:#x}]={}",
                    self.pc,
                    instruction_to_str(instruction),
                    base_address,
                    immediate,
                    itype.rd(),
                    address,
                    value,
                );

                self.assign_rd(itype.rd(), value);

                self.pc += INSTRUCTION_SIZE;
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
        if let Value::Concrete(base_address) = self.regs[stype.rs1() as usize] {
            let immediate = stype.imm();

            let address = base_address.wrapping_add(immediate as u64);

            let bug =
                self.check_for_valid_memory_address(instruction_to_str(instruction), address)?;

            if bug.is_none() {
                let value = self.regs[stype.rs2() as usize];

                trace!(
                    "[{:#010x}] {}: {:#x}, {}, {} |- mem[{:#x}] <- {}",
                    self.pc,
                    instruction_to_str(instruction),
                    base_address,
                    immediate,
                    self.regs[stype.rs2() as usize],
                    address,
                    value,
                );

                self.memory[(address / 8) as usize] = value;

                self.pc += INSTRUCTION_SIZE;
            }

            Ok(bug)
        } else {
            not_supported("can not handle symbolic addresses in SD")
        }
    }

    fn execute_jal(&mut self, jtype: JType) -> Result<Option<Bug>, EngineError> {
        let link = self.pc + INSTRUCTION_SIZE;

        let new_pc = self.pc.wrapping_add(jtype.imm() as u64);

        trace!(
            "[{:#010x}] jal: pc <- {:#x}, {:?} <- {:#x}",
            self.pc,
            new_pc,
            jtype.rd(),
            link,
        );

        self.pc = new_pc;

        self.assign_rd(jtype.rd(), Value::Concrete(link));

        Ok(None)
    }

    fn assign_rd(&mut self, rd: Register, v: Value) {
        if rd != Register::Zero {
            self.regs[rd as usize] = v;
        }
    }

    fn execute_jalr(&mut self, itype: IType) -> Result<Option<Bug>, EngineError> {
        if let Value::Concrete(dest) = self.regs[itype.rs1() as usize] {
            let link = self.pc + INSTRUCTION_SIZE;

            let new_pc = dest.wrapping_add(itype.imm() as u64);

            trace!(
                "[{:#010x}] jalr: {:#x}, {} |- pc <- {:#x}, {:?} <- {:#x}",
                self.pc,
                dest,
                itype.imm(),
                new_pc,
                itype.rd(),
                link
            );

            self.assign_rd(itype.rd(), Value::Concrete(link));

            self.pc = new_pc;

            Ok(None)
        } else {
            not_supported("can only handle concrete addresses in JALR")
        }
    }

    fn fetch(&self) -> Result<u32, EngineError> {
        if let Value::Concrete(dword) = self.memory[(self.pc as usize / size_of::<u64>()) as usize]
        {
            if self.pc % size_of::<u64>() as u64 == 0 {
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

pub const fn instruction_to_str(i: Instruction) -> &'static str {
    match i {
        Instruction::Lui(_) => "lui",
        Instruction::Jal(_) => "jal",
        Instruction::Jalr(_) => "jalr",
        Instruction::Beq(_) => "beq",
        Instruction::Ld(_) => "ld",
        Instruction::Sd(_) => "sd",
        Instruction::Addi(_) => "addi",
        Instruction::Add(_) => "add",
        Instruction::Sub(_) => "sub",
        Instruction::Sltu(_) => "sltu",
        Instruction::Mul(_) => "mul",
        Instruction::Divu(_) => "divu",
        Instruction::Remu(_) => "remu",
        Instruction::Ecall(_) => "ecall",
    }
}

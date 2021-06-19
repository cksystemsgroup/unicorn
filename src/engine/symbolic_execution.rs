use super::{
    bug::{Bug as GenericBug, BugInfo},
    profiler::Profiler,
    symbolic_state::{Condition, QueryResult, SymbolicState, SymbolicValue, Witness},
    system::{instruction_to_str, SyscallId},
    UninitializedMemoryAccessReason, VirtualMemory,
};
use crate::{
    path_exploration::ExplorationStrategy,
    solver::{BVOperator, Solver, SolverError},
    BugFinder,
};
use byteorder::{ByteOrder, LittleEndian};
use bytesize::ByteSize;
use log::{debug, trace};
use riscu::{
    decode, types::*, DecodingError, Instruction, Program, ProgramSegment, Register,
    INSTRUCTION_SIZE as INSTR_SIZE,
};
use std::{fmt, mem::size_of, sync::Arc};
use thiserror::Error;

const INSTRUCTION_SIZE: u64 = INSTR_SIZE as u64;

pub mod defaults {
    use super::*;

    pub const MEMORY_SIZE: ByteSize = ByteSize(bytesize::MIB);
    pub const MAX_EXECUTION_DEPTH: u64 = 1000;
    pub const OPTIMISTICALLY_PRUNE_SEARCH_SPACE: bool = true;
}

pub type SymbolicExecutionBug = GenericBug<SymbolicExecutionBugInfo>;
pub type SymbolicExecutionResult = Result<Option<SymbolicExecutionBug>, SymbolicExecutionError>;

type Bug = SymbolicExecutionBug;

#[derive(Clone, Copy, Debug)]
pub struct SymbolicExecutionOptions {
    pub memory_size: ByteSize,
    pub max_exection_depth: u64,
    pub optimistically_prune_search_space: bool,
}

impl Default for SymbolicExecutionOptions {
    fn default() -> Self {
        Self {
            memory_size: defaults::MEMORY_SIZE,
            max_exection_depth: defaults::MAX_EXECUTION_DEPTH,
            optimistically_prune_search_space: defaults::OPTIMISTICALLY_PRUNE_SEARCH_SPACE,
        }
    }
}

pub struct SymbolicExecutionEngine<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    options: SymbolicExecutionOptions,
    strategy: &'a E,
    solver: &'a S,
    profile: Option<Profiler>,
}

impl<'a, E, S> SymbolicExecutionEngine<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    pub fn new(options: &SymbolicExecutionOptions, strategy: &'a E, solver: &'a S) -> Self {
        Self {
            options: *options,
            strategy,
            solver,
            profile: None,
        }
    }

    pub fn profile(&self) -> Option<&Profiler> {
        self.profile.as_ref()
    }
}

impl<'a, E, S> BugFinder<SymbolicExecutionBugInfo, SymbolicExecutionError>
    for SymbolicExecutionEngine<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    fn search_for_bugs(
        &mut self,
        program: &Program,
    ) -> Result<Option<GenericBug<SymbolicExecutionBugInfo>>, SymbolicExecutionError> {
        let mut executor =
            SymbolicExecutor::new(program, &self.options, self.strategy, self.solver);

        let (result, t) = time!({ executor.run() });

        let mut profiler = (*executor.profile()).clone();

        profiler.allocated_memory(executor.memory.allocated());
        profiler.symbolic_execution_took(t);

        self.profile = Some(profiler);

        match result.expect_err("every run has to stop with an error") {
            SymbolicExecutionError::ExecutionDepthReached(_)
            | SymbolicExecutionError::ProgramExit(_)
            | SymbolicExecutionError::NotReachable => Ok(None),
            SymbolicExecutionError::BugFound(bug) => Ok(Some(bug)),
            err => Err(err),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Value {
    Concrete(u64),
    Symbolic(SymbolicValue),
    Uninitialized,
}

impl Default for Value {
    fn default() -> Self {
        Self::Uninitialized
    }
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

#[derive(Debug, Clone, Error)]
pub enum SymbolicExecutionError {
    #[error("failed to load binary {0:#}")]
    IoError(Arc<anyhow::Error>),

    #[error("engine does not support {0}")]
    NotSupported(String),

    #[error("has reached the maximum execution depth of {0}")]
    ExecutionDepthReached(u64),

    #[error("failed to decode instruction at PC: {0:#010x}")]
    InvalidInstructionEncoding(u64, DecodingError),

    #[error("fatal error in SMT solver")]
    Solver(SolverError),

    #[error("found a bug")]
    BugFound(Bug),

    #[error("exit syscall called with code: {0}")]
    ProgramExit(Value),

    #[error("program state is not reachable")]
    NotReachable,
}

pub struct SymbolicExecutor<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    symbolic_state: Box<SymbolicState<'a, S>>,
    program_break: u64,
    pc: u64,
    regs: [Value; 32],
    memory: VirtualMemory<Value>,
    strategy: &'a E,
    options: SymbolicExecutionOptions,
    execution_depth: u64,
    amount_of_file_descriptors: u64,
    profiler: Profiler,
}

impl<'a, E, S> SymbolicExecutor<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    // creates a machine state with a specific memory size
    pub fn new(
        program: &Program,
        options: &SymbolicExecutionOptions,
        strategy: &'a E,
        solver: &'a S,
    ) -> Self {
        let mut regs = [Value::Uninitialized; 32];
        let memory_size = options.memory_size.as_u64();
        let mut memory = VirtualMemory::new(memory_size as usize / size_of::<u64>(), 4096);

        let sp = memory_size - 8;
        regs[Register::Sp as usize] = Value::Concrete(sp);
        regs[Register::Zero as usize] = Value::Concrete(0);

        // TODO: Init main function arguments
        let argc = 0;
        memory[sp as usize / size_of::<u64>()] = Value::Concrete(argc);

        load_segment(&mut memory, &program.code);
        load_segment(&mut memory, &program.data);

        let pc = program.code.address;

        let program_break = program.data.address + program.data.content.len() as u64;

        let symbolic_state = Box::new(SymbolicState::new(solver));

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
            options: *options,
            // stdin (0), stdout (1), stderr (2) are already opened by the system
            amount_of_file_descriptors: 3,
            profiler: Profiler::new(),
        }
    }

    fn decode(&self, raw: u32) -> Result<Instruction, SymbolicExecutionError> {
        decode(raw).map_err(|e| SymbolicExecutionError::InvalidInstructionEncoding(self.pc, e))
    }

    fn run(&mut self) -> Result<(), SymbolicExecutionError> {
        loop {
            if self.execution_depth >= self.options.max_exection_depth {
                trace!("maximum execution depth reached => exiting this context");

                self.profiler.aborted_path_exploration(self.execution_depth);

                return Err(SymbolicExecutionError::ExecutionDepthReached(
                    self.execution_depth,
                ));
            }

            self.execution_depth += 1;

            self.fetch()
                .and_then(|raw| self.decode(raw))
                .and_then(|instr| self.execute(instr))?;
        }
    }

    pub fn profile(&self) -> &Profiler {
        &self.profiler
    }

    fn reachable(&mut self) -> Result<QueryResult, SymbolicExecutionError> {
        let (result, t) = time!({ self.symbolic_state.reachable() });

        result
            .map_err(SymbolicExecutionError::Solver)
            .map(|result| {
                self.profiler.solved_query(t, &result);

                result
            })
    }

    fn reachable_with(
        &mut self,
        cond: Condition,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) -> Result<QueryResult, SymbolicExecutionError> {
        let (result, t) = time!({ self.symbolic_state.reachable_with(cond, lhs, rhs) });

        result
            .map_err(SymbolicExecutionError::Solver)
            .map(|result| {
                self.profiler.solved_query(t, &result);

                result
            })
    }

    fn access_to_uninitialized_memory(
        &mut self,
        instruction: Instruction,
        v1: Value,
        v2: Value,
    ) -> Result<(), SymbolicExecutionError> {
        trace!(
            "{}: {}, {} => computing reachability",
            instruction_to_str(instruction),
            v1,
            v2
        );

        self.reachable().and_then(|result| {
            trace!("access to uninitialized memory => exiting");

            self.exit_anyway_with_bug(result, |t, w| {
                t.access_to_uninitialized_memory_bug(
                    w,
                    UninitializedMemoryAccessReason::InstructionWithUninitializedOperand {
                        instruction,
                        operands: vec![v1, v2],
                    },
                )
            })
        })
    }

    fn collect_bug_info(&self, witness: Option<Witness>) -> SymbolicExecutionBugInfo {
        SymbolicExecutionBugInfo {
            witness,
            pc: self.pc,
        }
    }

    fn access_to_unaligned_address_bug(&self, witness: Option<Witness>) -> Bug {
        Bug::AccessToUnalignedAddress {
            info: self.collect_bug_info(witness),
            address: self.pc,
        }
    }

    fn access_to_uninitialized_memory_bug(
        &self,
        witness: Option<Witness>,
        reason: UninitializedMemoryAccessReason<SymbolicExecutionBugInfo>,
    ) -> Bug {
        Bug::AccessToUnitializedMemory {
            info: self.collect_bug_info(witness),
            reason,
        }
    }

    fn access_to_out_of_range_address_bug(&self, witness: Option<Witness>) -> Bug {
        Bug::AccessToOutOfRangeAddress {
            info: self.collect_bug_info(witness),
        }
    }

    fn divison_by_zero_bug(&self, witness: Option<Witness>) -> Bug {
        Bug::DivisionByZero {
            info: self.collect_bug_info(witness),
        }
    }

    fn exit_code_greater_zero_bug(&self, witness: Option<Witness>, exit_code: Value) -> Bug {
        Bug::ExitCodeGreaterZero {
            info: self.collect_bug_info(witness),
            exit_code,
            address: self.pc,
        }
    }

    fn exit_regularly(&mut self) -> Result<(), SymbolicExecutionError> {
        self.profiler.end_of_path(self.execution_depth);

        Err(SymbolicExecutionError::ProgramExit(Value::Concrete(0)))
    }

    fn exit_anyway_with_bug<F>(
        &mut self,
        result: QueryResult,
        create_bug: F,
    ) -> Result<(), SymbolicExecutionError>
    where
        F: FnOnce(&mut Self, Option<Witness>) -> Bug,
    {
        self.profiler.end_of_path(self.execution_depth);

        let witness = match result {
            QueryResult::Sat(w) => Some(w),
            QueryResult::UnSat | QueryResult::Unknown => None,
        };

        let bug = create_bug(self, witness);

        Err(SymbolicExecutionError::BugFound(bug))
    }

    fn exit_anyway_with_bug_if_sat<F>(
        &mut self,
        result: QueryResult,
        create_bug: F,
        err_if_unsat: SymbolicExecutionError,
    ) -> Result<(), SymbolicExecutionError>
    where
        F: FnOnce(&mut Self, Option<Witness>) -> Bug,
    {
        self.profiler.end_of_path(self.execution_depth);

        match result {
            QueryResult::Sat(witness) => Err(SymbolicExecutionError::BugFound(create_bug(
                self,
                Some(witness),
            ))),
            QueryResult::UnSat | QueryResult::Unknown => Err(err_if_unsat),
        }
    }

    fn exit_with_bug_if_sat<F>(
        &mut self,
        result: QueryResult,
        create_bug: F,
    ) -> Result<(), SymbolicExecutionError>
    where
        F: FnOnce(&mut Self, Option<Witness>) -> Bug,
    {
        match result {
            QueryResult::Sat(witness) => {
                let bug = create_bug(self, Some(witness));

                self.profiler.end_of_path(self.execution_depth);

                Err(SymbolicExecutionError::BugFound(bug))
            }
            QueryResult::UnSat | QueryResult::Unknown => Ok(()),
        }
    }

    fn exit_with_unsupported(&mut self, s: String) -> Result<(), SymbolicExecutionError> {
        self.profiler.aborted_path_exploration(self.execution_depth);

        Err(SymbolicExecutionError::NotSupported(s))
    }

    fn is_in_vaddr_range(&self, vaddr: u64) -> bool {
        vaddr as usize / size_of::<u64>() < self.memory.size()
    }

    fn check_for_valid_memory_address(
        &mut self,
        instruction: &str,
        address: u64,
    ) -> Result<(), SymbolicExecutionError> {
        let is_alignment_ok = address % size_of::<u64>() as u64 == 0;

        if !is_alignment_ok {
            trace!(
                "{}: address {:#x} is not double word aligned => computing reachability",
                instruction,
                address
            );

            self.reachable().and_then(|r| {
                self.exit_anyway_with_bug(r, |t, w| t.access_to_unaligned_address_bug(w))
            })
        } else if !self.is_in_vaddr_range(address) {
            trace!(
                "{}: address {:#x} out of virtual address range (0x0 - {:#x}) => computing reachability",
                instruction,
                address,
                self.memory.size() * size_of::<u64>(),
            );

            self.reachable().and_then(|r| {
                self.exit_anyway_with_bug(r, |t, w| t.access_to_out_of_range_address_bug(w))
            })
        } else {
            Ok(())
        }
    }

    fn check_for_valid_memory_range(
        &mut self,
        instruction: &str,
        address: u64,
        size: u64,
    ) -> Result<(), SymbolicExecutionError> {
        if !self.is_in_vaddr_range(address) || !self.is_in_vaddr_range(address + size) {
            trace!(
                "{}: buffer {:#x} - {:#x} out of virtual address range (0x0 - {:#x}) => computing reachability",
                instruction,
                address,
                address + size,
                self.memory.size() * size_of::<u64>(),
            );

            self.reachable().and_then(|r| {
                self.exit_anyway_with_bug(r, |t, w| t.access_to_out_of_range_address_bug(w))
            })
        } else {
            Ok(())
        }
    }

    #[allow(clippy::unnecessary_wraps)]
    fn execute_lui(&mut self, utype: UType) -> Result<(), SymbolicExecutionError> {
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

        Ok(())
    }

    fn execute_divu_remu<Op>(
        &mut self,
        instruction: Instruction,
        rtype: RType,
        op: Op,
    ) -> Result<(), SymbolicExecutionError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        match self.regs[rtype.rs2() as usize] {
            Value::Symbolic(divisor) => {
                trace!(
                    "{}: symbolic divisor -> find input for divisor == 0",
                    instruction_to_str(instruction)
                );

                self.reachable_with(Condition::Equals, divisor, self.symbolic_state.zero())
                    .and_then(|r| self.exit_with_bug_if_sat(r, |t, w| t.divison_by_zero_bug(w)))?;

                self.symbolic_state.add_path_condition(
                    Condition::NotEquals,
                    divisor,
                    self.symbolic_state.zero(),
                );
            }
            Value::Concrete(divisor) if divisor == 0 => {
                trace!(
                    "{}: divisor == 0 -> compute reachability",
                    instruction_to_str(instruction)
                );

                return self
                    .reachable()
                    .and_then(|r| self.exit_anyway_with_bug(r, |t, w| t.divison_by_zero_bug(w)));
            }
            _ => {}
        };

        self.execute_rtype(instruction, rtype, op)
    }

    fn execute_itype<Op>(
        &mut self,
        instruction: Instruction,
        itype: IType,
        op: Op,
    ) -> Result<(), SymbolicExecutionError>
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
    ) -> Result<(), SymbolicExecutionError>
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
    ) -> Result<(), SymbolicExecutionError>
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
                return self.access_to_uninitialized_memory(instruction, lhs, rhs);
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

        Ok(())
    }

    fn execute_brk(&mut self) -> Result<(), SymbolicExecutionError> {
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

            Ok(())
        } else {
            self.exit_with_unsupported(
                "can not handle symbolic or uninitialized program break".into(),
            )
        }
    }

    fn bytewise_combine(
        &mut self,
        old: Value,
        n_lower_bytes: u32,
        new_idx: SymbolicValue,
    ) -> SymbolicValue {
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

    fn execute_openat(&mut self) -> Result<(), SymbolicExecutionError> {
        // C signature: int openat(int dirfd, const char *pathname, int flags, mode_t mode)

        let dirfd = if let Value::Concrete(d) = self.regs[Register::A0 as usize] {
            d
        } else {
            return self.exit_with_unsupported(
                "can only handle concrete values for dirfd in openat syscall".into(),
            );
        };

        let pathname = if let Value::Concrete(p) = self.regs[Register::A1 as usize] {
            p
        } else {
            return self.exit_with_unsupported(
                "can only handle concrete values for pathname in openat syscall".into(),
            );
        };

        let flags = if let Value::Concrete(f) = self.regs[Register::A2 as usize] {
            f
        } else {
            return self.exit_with_unsupported(
                "can only handle concrete values for flags in openat syscall".into(),
            );
        };

        let mode = if let Value::Concrete(m) = self.regs[Register::A3 as usize] {
            m
        } else {
            return self.exit_with_unsupported(
                "can only handle concrete values for mode in openat syscall".into(),
            );
        };

        // TODO: read actual C-string from virtual memory
        trace!(
            "openat: dirfd={} pathname={} flags={} mode={}",
            dirfd,
            pathname,
            flags,
            mode
        );

        self.regs[Register::A0 as usize] = Value::Concrete(self.amount_of_file_descriptors);

        self.amount_of_file_descriptors += 1;

        Ok(())
    }

    fn execute_read(&mut self) -> Result<(), SymbolicExecutionError> {
        if !matches!(self.regs[Register::A0 as usize], Value::Concrete(0)) {
            return self.exit_with_unsupported(
                "can not handle fd other than stdin in read syscall".into(),
            );
        }

        let buffer = if let Value::Concrete(b) = self.regs[Register::A1 as usize] {
            b
        } else {
            return self.exit_with_unsupported(
                "can not handle symbolic or uninitialized buffer address in read syscall".into(),
            );
        };

        let size = if let Value::Concrete(s) = self.regs[Register::A2 as usize] {
            s
        } else {
            return self.exit_with_unsupported(
                "can not handle symbolic or uinitialized size in read syscall".into(),
            );
        };

        trace!("read: fd={} buffer={:#x} size={}", 0, buffer, size,);

        self.check_for_valid_memory_range("read", buffer, size)?;

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

            let addr = (start + word_count) as usize;

            let result_idx = if bytes_to_read >= size_of_u64 {
                bytes_to_read -= size_of_u64;

                input_idx
            } else {
                match self.memory[addr] {
                    Value::Uninitialized => {
                        // we do not partially overwrite words with concrete values
                        // if at least one byte in a word is uninitialized, the whole word is uninitialized
                        break;
                    }
                    v => self.bytewise_combine(v, bytes_to_read as u32, input_idx),
                }
            };

            self.memory[addr] = Value::Symbolic(result_idx);
        }

        self.regs[Register::A0 as usize] = Value::Concrete(size);

        Ok(())
    }

    fn execute_write(&mut self) -> Result<(), SymbolicExecutionError> {
        if !matches!(self.regs[Register::A0 as usize], Value::Concrete(1)) {
            return self.exit_with_unsupported(
                "can not handle fd other than stdout in write syscall".into(),
            );
        }

        let buffer = if let Value::Concrete(b) = self.regs[Register::A1 as usize] {
            b
        } else {
            return self.exit_with_unsupported(
                "can not handle symbolic or uninitialized buffer address in write syscall".into(),
            );
        };

        let size = if let Value::Concrete(s) = self.regs[Register::A2 as usize] {
            s
        } else {
            return self.exit_with_unsupported(
                "can not handle symbolic or uinitialized size in write syscall".into(),
            );
        };

        trace!("write: fd={} buffer={:#x} size={}", 1, buffer, size,);

        self.check_for_valid_memory_range("write", buffer, size)?;

        let size_of_u64 = size_of::<u64>() as u64;
        let start = buffer / size_of_u64;
        let bytes_to_read = size + buffer % size_of_u64;
        let words_to_read = (bytes_to_read + size_of_u64 - 1) / size_of_u64;

        for word_count in 0..words_to_read {
            let address = start + word_count;

            if self.memory[address as usize] == Value::Uninitialized {
                trace!(
                    "write: access to uninitialized memory at {:#x} => computing reachability",
                    (start + word_count) * size_of_u64,
                );

                return self.reachable().and_then(|r| {
                    self.exit_anyway_with_bug(r, |t, w| {
                        t.access_to_uninitialized_memory_bug(
                            w,
                            UninitializedMemoryAccessReason::ReadUnintializedMemoryAddress {
                                description: format!(
                                    "access to uninitialized memory at address: {:#x}",
                                    address
                                ),
                                address,
                            },
                        )
                    })
                });
            }
        }

        self.regs[Register::A0 as usize] = Value::Concrete(size);

        Ok(())
    }

    fn should_execute_branch(&mut self) -> Result<(bool, &'static str), SymbolicExecutionError> {
        let result = self.reachable()?;

        self.profiler.solved_branch_decision_query();

        Ok(match result {
            QueryResult::Sat(_) => (true, "reachable"),
            QueryResult::Unknown if !self.options.optimistically_prune_search_space => {
                (true, "reachability unknown")
            }
            _ => (false, "unreachable"),
        })
    }

    fn with_snapshot<F, R>(&mut self, f: F) -> (R, Profiler)
    where
        F: FnOnce(&mut Self) -> R,
    {
        let memory_snapshot = self.memory.clone();
        let regs_snapshot = self.regs;
        let graph_snapshot = Box::new((*self.symbolic_state).clone());
        let brk_snapshot = self.program_break;
        let execution_depth_snapshot = self.execution_depth;
        let amount_of_file_descriptors_snapshot = self.amount_of_file_descriptors;
        let profiler_snapshot = self.profiler.clone();

        let result = f(self);
        let profiler = self.profiler.clone();

        self.memory = memory_snapshot;
        self.regs = regs_snapshot;
        self.symbolic_state = graph_snapshot;
        self.program_break = brk_snapshot;
        self.execution_depth = execution_depth_snapshot;
        self.amount_of_file_descriptors = amount_of_file_descriptors_snapshot;
        self.profiler = profiler_snapshot;

        (result, profiler)
    }

    fn execute_beq_branches(
        &mut self,
        true_branch: u64,
        false_branch: u64,
        lhs: SymbolicValue,
        rhs: SymbolicValue,
    ) -> Result<(), SymbolicExecutionError> {
        self.profiler.beq_with_symbolic_condition();

        let next_pc = self.strategy.choose_path(true_branch, false_branch);

        let decision = next_pc == true_branch;

        let (result_first_branch, mut profiler_first_branch) =
            self.with_snapshot(|this| -> Result<(), SymbolicExecutionError> {
                this.symbolic_state.add_path_condition(
                    if decision {
                        Condition::Equals
                    } else {
                        Condition::NotEquals
                    },
                    lhs,
                    rhs,
                );

                let (execute_branch, reachability) = this.should_execute_branch()?;

                if execute_branch {
                    trace!(
                        "[{:#010x}] beq: x{}, x{} |- assume {} ({}), pc <- {:#x}",
                        this.pc,
                        lhs.index(),
                        rhs.index(),
                        decision,
                        reachability,
                        next_pc,
                    );

                    this.profiler = Profiler::new();
                    this.profiler.took_beq_branch(decision);

                    this.pc = next_pc;

                    this.run()
                } else {
                    trace!(
                        "[{:#010x}] beq: x{}, x{} |- assume {} ({}), skip branch",
                        this.pc,
                        lhs.index(),
                        rhs.index(),
                        decision,
                        reachability
                    );

                    Err(SymbolicExecutionError::NotReachable)
                }
            });

        self.profiler.merge_with(&mut profiler_first_branch);

        let potential_symbolic_path_explosion = match result_first_branch {
            Ok(_) => panic!("every branch execution has to end with an error"),
            Err(SymbolicExecutionError::ExecutionDepthReached(_))
            | Err(SymbolicExecutionError::ProgramExit(_)) => true,
            Err(SymbolicExecutionError::NotReachable) => false,
            err => {
                return err;
            }
        };

        let next_pc = if decision { false_branch } else { true_branch };

        self.symbolic_state.add_path_condition(
            if !decision {
                Condition::Equals
            } else {
                Condition::NotEquals
            },
            lhs,
            rhs,
        );

        let (execute_branch, reachability) = self.should_execute_branch()?;

        if execute_branch {
            trace!(
                "[{:#010x}] beq: x{}, x{} |- assume {} ({}), pc <- {:#x}",
                self.pc,
                lhs.index(),
                rhs.index(),
                !decision,
                reachability,
                next_pc,
            );

            if potential_symbolic_path_explosion {
                self.profiler.symbolic_path_explosion();
            }

            self.profiler.took_beq_branch(!decision);

            self.pc = next_pc;

            Ok(())
        } else {
            trace!(
                "[{:#010x}] beq: x{}, x{} |- assume {} ({}), skip branch",
                self.pc,
                lhs.index(),
                rhs.index(),
                !decision,
                reachability
            );

            result_first_branch
        }
    }

    fn execute_beq(&mut self, btype: BType) -> Result<(), SymbolicExecutionError> {
        let lhs = self.regs[btype.rs1() as usize];
        let rhs = self.regs[btype.rs2() as usize];

        let true_branch = self.pc.wrapping_add(btype.imm() as u64);
        let false_branch = self.pc.wrapping_add(INSTRUCTION_SIZE);

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

                Ok(())
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
            (v1, v2) => self.access_to_uninitialized_memory(Instruction::Beq(btype), v1, v2),
        }
    }

    fn execute_exit(&mut self) -> Result<(), SymbolicExecutionError> {
        match self.regs[Register::A0 as usize] {
            Value::Symbolic(exit_code) => {
                trace!("exit: symbolic code -> find input for exit_code != 0");

                self.reachable_with(Condition::NotEquals, exit_code, self.symbolic_state.zero())
                    .and_then(|r| {
                        self.exit_anyway_with_bug_if_sat(
                            r,
                            |t, w| t.exit_code_greater_zero_bug(w, Value::Symbolic(exit_code)),
                            SymbolicExecutionError::ProgramExit(Value::Symbolic(exit_code)),
                        )
                    })
            }
            Value::Concrete(exit_code) => {
                if exit_code > 0 {
                    trace!(
                        "exit: with code {} -> find input to satisfy path condition",
                        exit_code
                    );

                    self.reachable().and_then(|r| {
                        self.exit_anyway_with_bug(r, |t, w| {
                            t.exit_code_greater_zero_bug(w, Value::Concrete(exit_code))
                        })
                    })
                } else {
                    trace!("exit: with code 0");

                    self.exit_regularly()
                }
            }
            _ => self.exit_with_unsupported("exit only implemented for symbolic exit codes".into()),
        }
    }

    fn execute_ecall(&mut self) -> Result<(), SymbolicExecutionError> {
        trace!("[{:#010x}] ecall", self.pc);

        let result = match self.regs[Register::A7 as usize] {
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Brk as u64) => {
                self.execute_brk()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Openat as u64) => {
                self.execute_openat()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Read as u64) => {
                self.execute_read()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Write as u64) => {
                self.execute_write()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Exit as u64) => {
                self.execute_exit()
            }
            id => self.exit_with_unsupported(format!("syscall with id ({}) is not supported", id)),
        };

        self.pc += INSTRUCTION_SIZE;

        result
    }

    fn execute_ld(
        &mut self,
        instruction: Instruction,
        itype: IType,
    ) -> Result<(), SymbolicExecutionError> {
        if let Value::Concrete(base_address) = self.regs[itype.rs1() as usize] {
            let immediate = itype.imm() as u64;

            let address = base_address.wrapping_add(immediate);

            self.check_for_valid_memory_address(instruction_to_str(instruction), address)?;

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

            Ok(())
        } else {
            self.exit_with_unsupported("can not handle symbolic addresses in LD".into())
        }
    }

    fn execute_sd(
        &mut self,
        instruction: Instruction,
        stype: SType,
    ) -> Result<(), SymbolicExecutionError> {
        if let Value::Concrete(base_address) = self.regs[stype.rs1() as usize] {
            let immediate = stype.imm();

            let address = base_address.wrapping_add(immediate as u64);

            self.check_for_valid_memory_address(instruction_to_str(instruction), address)?;

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

            Ok(())
        } else {
            self.exit_with_unsupported("can not handle symbolic addresses in SD".into())
        }
    }

    #[allow(clippy::unnecessary_wraps)]
    fn execute_jal(&mut self, jtype: JType) -> Result<(), SymbolicExecutionError> {
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

        Ok(())
    }

    fn assign_rd(&mut self, rd: Register, v: Value) {
        if rd != Register::Zero {
            self.regs[rd as usize] = v;
        }
    }

    fn execute_jalr(&mut self, itype: IType) -> Result<(), SymbolicExecutionError> {
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

            Ok(())
        } else {
            self.exit_with_unsupported("can only handle concrete addresses in JALR".into())
        }
    }

    fn fetch(&mut self) -> Result<u32, SymbolicExecutionError> {
        if let Value::Concrete(dword) = self.memory[(self.pc as usize / size_of::<u64>()) as usize]
        {
            if self.pc % size_of::<u64>() as u64 == 0 {
                Ok(dword as u32)
            } else {
                Ok((dword >> 32) as u32)
            }
        } else {
            Err(self
                .exit_with_unsupported("tried to fetch none concrete instruction".into())
                .unwrap_err())
        }
    }

    fn execute(&mut self, instruction: Instruction) -> Result<(), SymbolicExecutionError> {
        let res = match instruction {
            Instruction::Ecall(_) => self.execute_ecall(),
            Instruction::Lui(utype) => self.execute_lui(utype),
            Instruction::Addi(itype) => self.execute_itype(instruction, itype, u64::wrapping_add),
            Instruction::Add(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_add),
            Instruction::Sub(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_sub),
            Instruction::Mul(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_mul),
            Instruction::Divu(rtype) => {
                self.execute_divu_remu(instruction, rtype, u64::wrapping_div)
            }
            Instruction::Remu(rtype) => {
                self.execute_divu_remu(instruction, rtype, u64::wrapping_rem)
            }
            Instruction::Sltu(rtype) => {
                self.execute_rtype(instruction, rtype, |l, r| if l < r { 1 } else { 0 })
            }
            Instruction::Ld(itype) => self.execute_ld(instruction, itype),
            Instruction::Sd(stype) => self.execute_sd(instruction, stype),
            Instruction::Jal(jtype) => self.execute_jal(jtype),
            Instruction::Jalr(itype) => self.execute_jalr(itype),
            Instruction::Beq(btype) => self.execute_beq(btype),
        };

        self.profiler.instruction_executed();

        res
    }
}

fn load_segment(memory: &mut VirtualMemory<Value>, segment: &ProgramSegment<u8>) {
    let start = segment.address as usize / size_of::<u64>();
    let end = start + segment.content.len() / size_of::<u64>();

    segment
        .content
        .chunks(size_of::<u64>())
        .map(LittleEndian::read_u64)
        .zip(start..end)
        .for_each(|(x, i)| memory[i] = Value::Concrete(x));
}

#[derive(Debug, Clone)]
pub struct SymbolicExecutionBugInfo {
    pub witness: Option<Witness>,
    pub pc: u64,
}

impl BugInfo for SymbolicExecutionBugInfo {
    type Value = Value;
}

impl fmt::Display for SymbolicExecutionBugInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "pc: {:#010x}", self.pc)?;

        if let Some(witness) = &self.witness {
            write!(f, "\nwitness: {}", witness)
        } else {
            Ok(())
        }
    }
}

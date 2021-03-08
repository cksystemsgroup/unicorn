//! Rarity Simulation
//!
//! This module contains an implementation of rarity simulation, as descibed in the paper ["Using Speculation for Sequential Equivalence Checking"
//! ](https://people.eecs.berkeley.edu/~alanmi/publications/2012/iwls12_sec.pdf) by
//! Brayton et. al.
//!
//!
//! Rarity simulation is a "guided random simulation" using heuristics to determine interesting
//! states and which aims to reduce the time required to find bugs in a target application.
//! Instead of symbolically pursuing all control branches and recording constraints, it concretely
//! executes a fixed number of states. On each iteration, rarity simulation advances each state by
//! a fixed amount of instruction cycles and records statistics which values were encountered over
//! the entire execution state. Furthermore, at the end of the iteration, it uses the recorded
//! statistics to determine the _rarity_ of each state and only pursues a subset of rarest states,
//! all other states are discarded and new states are copied from the remaining states or created
//! to reach the number of states.
//! Rarity simulation interations are repeated until a bug in any state is encountered or a
//! specific amount of iterations have been completed.
//!
//!
//! To archive divergent states, the target application shall issue word-granularity `read()`
//! system calls to receive random input values. Rarity simulation stores a list of subsequent
//! inputs that were provided to the application. In case a state caused a bug, it is able to
//! provide a list of inputs which provoke the bug.
//!
//! The amount of iterations/cycles and the amount of states allows for a fine-grained control for
//! finding bugs in depth or in breadth, respectively.

use super::{
    system::{instruction_to_str, SyscallId},
    Bug as GenericBug, BugFinder, BugInfo,
};
use byteorder::{ByteOrder, LittleEndian};
use bytesize::ByteSize;
use itertools::Itertools;
use log::{debug, info, trace, warn};
use riscu::{
    decode, types::*, DecodingError, Instruction, Program, ProgramSegment, Register,
    INSTRUCTION_SIZE as INSTR_SIZE,
};
use std::{
    cmp::{min, Ordering},
    collections::HashMap,
    fmt,
    iter::IntoIterator,
    mem::size_of,
    sync::Arc,
};
use strum::{EnumString, EnumVariantNames, IntoStaticStr};
use thiserror::Error;

pub type RaritySimulationBug = GenericBug<RarityBugInfo>;
type Bug = RaritySimulationBug;

type ExecutorResult = Result<Option<RaritySimulationBug>, RaritySimulationError>;

const INSTRUCTION_SIZE: u64 = INSTR_SIZE as u64;

const BYTES_PER_WORD: u64 = size_of::<u64>() as u64;
const NUMBER_OF_BYTE_VALUES: u64 = 256;

pub mod defaults {
    use super::*;

    pub const MEMORY_SIZE: ByteSize = ByteSize(bytesize::MB);
    pub const AMOUNT_OF_STATES: usize = 3000;
    pub const STEP_SIZE: u64 = 1000;
    pub const SELECTION: usize = 50;
    pub const ITERATIONS: u64 = 20;
    pub const COPY_INIT_RATIO: f64 = 0.6;
    pub const MEAN_TYPE: MeanType = MeanType::Harmonic;
}

#[derive(Debug, Clone)]
pub struct RaritySimulationOptions {
    /// The size of the machine's memory
    pub memory_size: ByteSize,
    /// The number of states to pursue
    pub amount_of_states: usize,
    /// The amount of instructions to execute for each state on each iteration
    pub step_size: u64,
    /// Amount of (rarest) states that shall be further considered at the end of each iteration.
    pub selection: usize,
    /// The amount of rarity simulation iterations to perform
    pub iterations: u64,
    /// After discarding least rare and exited states, determines how much new states shall
    /// be copied from the remaining (rare) states and, in inverse, how much shall be newly
    /// created relative to the amount of missing states to archive `number_of_states`.
    /// Must be between 0 and 1.
    pub copy_init_ratio: f64,
    /// The mean to use for determining state rarity
    pub mean: MeanType,
}

impl Default for RaritySimulationOptions {
    fn default() -> RaritySimulationOptions {
        RaritySimulationOptions {
            memory_size: defaults::MEMORY_SIZE,
            amount_of_states: defaults::AMOUNT_OF_STATES,
            step_size: defaults::STEP_SIZE,
            selection: defaults::SELECTION,
            iterations: defaults::ITERATIONS,
            copy_init_ratio: defaults::COPY_INIT_RATIO,
            mean: defaults::MEAN_TYPE,
        }
    }
}

#[derive(Debug, Clone, Error)]
pub enum RaritySimulationError {
    #[error("failed to write State to file")]
    IoError(Arc<std::io::Error>),

    #[error("engine does not support {0}")]
    NotSupported(String),

    #[error("failed to decode instruction at PC: {0:#010x}")]
    InvalidInstructionEncoding(u64, DecodingError),

    #[error("has reached the maximum execution depth of {0}")]
    ExecutionDepthReached(u64),
}

/// Strategy for mean calculation
///
/// Based on the value counters, the rarity simulator calculates a score that is used to determine
/// a state's rarity. This score is essential for the decision which states shall be further
/// pursued and which shall be discarded.
#[derive(Clone, Copy, Debug, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum MeanType {
    /// Mean is calculated using the [arithmetic
    /// mean](https://en.wikipedia.org/wiki/Arithmetic_mean), i.e. the sum of all statistic
    /// counters divided by the amount of states.
    /// Lower scores are more rare
    Arithmetic,
    /// Mean is calculated using the [harmonic mean](https://en.wikipedia.org/wiki/Harmonic_mean),
    /// i.e. the amount of states divided by the sum of residues of statistic counters.
    /// Higher scores are more rare.
    Harmonic,
}

/// The state information of a running target
///
/// The [`State`] struct contains all necessary state information of a running target application,
/// similar to an operating system's context. Values are stored using the [`Value`] type. Only if a
/// location has been written to, it hosts a concrete value ([`Value::Concrete`]), otherwise it is
/// [`Value::Uninitialized`].
#[derive(Debug, Clone)]
pub struct State {
    /// Program counter
    pc: u64,
    /// Processor integer registers x0..x31
    regs: [Value; 32],
    /// List of touched and untouched memory words
    memory: Vec<Value>,
}

type Address = u64;
type Counter = u64;

#[derive(Debug, Clone)]
pub struct RaritySimulation {
    options: RaritySimulationOptions,
}

impl RaritySimulation {
    pub fn new(options: &RaritySimulationOptions) -> Self {
        Self {
            options: options.clone(),
        }
    }
}

impl BugFinder<RarityBugInfo, RaritySimulationError> for RaritySimulation {
    /// Performs rarity simulation on a given program
    ///
    /// If one state encountered a bug, execution is terminated and its description is returned. If no
    /// bugs have been encountered after the configured limit has been met, [`None`] is returned.
    ///
    /// Please see the [module-level documentation](self) for a detailed description of rarity simulation.
    #[allow(clippy::vec_box)]
    fn search_for_bugs(&self, program: &Program) -> Result<Option<Bug>, RaritySimulationError> {
        let mut executors: Vec<Box<Executor>> = Vec::new();

        for iteration in 0..self.options.iterations {
            info!("Running rarity simulation round {}...", iteration + 1);

            create_missing_executors(
                &mut executors,
                self.options.amount_of_states,
                self.options.copy_init_ratio,
                self.options.memory_size,
                program,
            );

            let results = time_info!("Running engines", {
                match run_all(&mut executors, self.options.step_size) {
                    Ok((Some(bug), _)) => return Ok(Some(bug)),
                    Ok((None, results)) => results,
                    Err(e) => return Err(e),
                }
            });

            let running = filter_successfully_exited(executors, results);

            info!(
                "Remove {} successfully exited states from selection",
                self.options.amount_of_states - running.len()
            );

            let (scores, ordering) = time_info!("Scoring states", {
                let states: Vec<_> = running.iter().map(|e| e.state()).collect();

                score_with_mean(&states[..], self.options.mean)
            });

            let selection = min(self.options.selection, running.len());

            executors = select_rarest(running, selection, scores, ordering);

            info!("selecting rarest {} states", selection);
        }

        Ok(None)
    }
}

#[allow(clippy::vec_box)]
fn create_missing_executors(
    executors: &mut Vec<Box<Executor>>,
    amount: usize,
    copy_init_ratio: f64,
    memory_size: ByteSize,
    program: &Program,
) {
    let missing = amount - executors.len();

    let to_copy = if executors.is_empty() {
        0
    } else {
        f64::round(missing as f64 * copy_init_ratio) as usize
    };
    let to_create = missing - to_copy;

    info!(
        "Creating {} new states ({} copied, {} new)",
        missing, to_copy, to_create
    );

    let copyable_engines = executors.len();

    let copied = (0..to_copy)
        .map(|_| Box::new((*executors[random_index(copyable_engines)]).clone()))
        .collect_vec();

    let created = (0..to_create).map(|_| Box::new(Executor::new(program, memory_size)));

    executors.extend(copied.into_iter().chain(created));
}

fn run_all(
    executors: &mut [Box<Executor>],
    step_size: u64,
) -> Result<(Option<RaritySimulationBug>, Vec<ExecutorResult>), RaritySimulationError> {
    let results: Vec<_> = executors
        .iter_mut()
        .map(|engine| engine.run(step_size))
        .collect();

    if let Some(Ok(Some(bug))) = results.iter().find(|r| matches!(r, Ok(Some(_)))) {
        Ok((Some(bug.clone()), results))
    } else if let Some(Err(e)) = results.iter().find(|r| match **r {
        Err(RaritySimulationError::ExecutionDepthReached(_)) => false,
        Err(_) => true,
        _ => false,
    }) {
        Err(e.clone())
    } else {
        Ok((None, results))
    }
}

#[allow(clippy::vec_box)]
fn filter_successfully_exited(
    executors: impl IntoIterator<Item = Box<Executor>>,
    results: impl IntoIterator<Item = ExecutorResult>,
) -> Vec<Box<Executor>> {
    executors
        .into_iter()
        .zip(results)
        .filter(|(_, r)| matches!(r, Err(RaritySimulationError::ExecutionDepthReached(_))))
        .map(|(e, _)| e)
        .collect()
}

#[allow(clippy::vec_box)]
fn select_rarest(
    executors: impl IntoIterator<Item = Box<Executor>>,
    selection: usize,
    scores: Vec<f64>,
    ord: Ordering,
) -> Vec<Box<Executor>> {
    let iter = executors.into_iter().zip(scores);

    let sorted = if ord == Ordering::Less {
        iter.sorted_unstable_by(|l, r| l.1.partial_cmp(&r.1).expect("no NaN in scores"))
    } else {
        iter.sorted_unstable_by(|l, r| r.1.partial_cmp(&l.1).expect("no NaN in scores"))
    };

    sorted.map(|x| x.0).take(selection).collect()
}

fn score_with_mean(states: &[&State], mean: MeanType) -> (Vec<f64>, Ordering) {
    match mean {
        MeanType::Harmonic => {
            let scores = compute_scores(states, |n, cs| {
                (n as f64) / cs.iter().map(|c| 1_f64 / (*c as f64)).sum::<f64>()
            });

            (scores, Ordering::Greater)
        }
        MeanType::Arithmetic => {
            let scores = compute_scores(states, |n, cs| cs.iter().sum::<u64>() as f64 / (n as f64));

            (scores, Ordering::Less)
        }
    }
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
pub struct Executor {
    program_break: u64,
    state: State,
    execution_depth: u64,
    max_exection_depth: u64,
    concrete_inputs: Vec<u64>,
    is_running: bool,
}

impl Executor {
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

    pub fn run(
        &mut self,
        number_of_instructions: u64,
    ) -> Result<Option<Bug>, RaritySimulationError> {
        self.is_running = true;
        self.max_exection_depth += number_of_instructions;

        loop {
            if self.execution_depth >= self.max_exection_depth {
                trace!("maximum execution depth reached => exiting this context");

                self.is_running = false;

                return Err(RaritySimulationError::ExecutionDepthReached(
                    self.execution_depth,
                ));
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

    fn fetch(&self) -> Result<u32, RaritySimulationError> {
        if let Value::Concrete(dword) =
            self.state.memory[(self.state.pc as usize / size_of::<u64>()) as usize]
        {
            if self.state.pc % size_of::<u64>() as u64 == 0 {
                Ok(dword as u32)
            } else {
                Ok((dword >> 32) as u32)
            }
        } else {
            Err(RaritySimulationError::NotSupported(String::from(
                "tried to fetch none concrete instruction",
            )))
        }
    }

    fn decode(&self, raw: u32) -> Result<Instruction, RaritySimulationError> {
        decode(raw).map_err(|e| RaritySimulationError::InvalidInstructionEncoding(self.state.pc, e))
    }

    fn execute(&mut self, instruction: Instruction) -> Result<Option<Bug>, RaritySimulationError> {
        match instruction {
            Instruction::Ecall(_) => self.execute_ecall(instruction),
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
        }
    }

    fn access_to_uninitialized_memory(
        &mut self,
        instruction: Instruction,
        v1: Value,
        v2: Value,
    ) -> Bug {
        trace!(
            "{}: {}, {} => computing reachability",
            instruction_to_str(instruction),
            v1,
            v2
        );

        Bug::AccessToUnitializedMemory {
            info: RarityBugInfo {
                inputs: self.concrete_inputs.clone(),
                pc: self.state.pc,
            },
            instruction,
            // TODO: fix operands
            operands: vec![],
        }
    }

    fn is_in_vaddr_range(&self, vaddr: u64) -> bool {
        vaddr as usize / size_of::<u64>() < self.state.memory.len()
    }

    fn check_for_valid_memory_address(&mut self, instruction: &str, address: u64) -> Option<Bug> {
        let is_alignment_ok = address % size_of::<u64>() as u64 == 0;

        if !is_alignment_ok {
            trace!(
                "{}: address {:#x} is not double word aligned => computing reachability",
                instruction,
                address
            );

            self.is_running = false;

            Some(Bug::AccessToUnalignedAddress {
                info: RarityBugInfo {
                    inputs: self.concrete_inputs.clone(),
                    pc: self.state.pc,
                },
                address,
            })
        } else if !self.is_in_vaddr_range(address) {
            trace!(
                "{}: address {:#x} out of virtual address range (0x0 - {:#x}) => computing reachability",
                instruction,
                address,
                self.state.memory.len() * 8,
            );

            self.is_running = false;

            Some(Bug::AccessToOutOfRangeAddress {
                info: RarityBugInfo {
                    inputs: self.concrete_inputs.clone(),
                    pc: self.state.pc,
                },
            })
        } else {
            None
        }
    }

    fn check_for_valid_memory_range(
        &mut self,
        instruction: &str,
        address: u64,
        size: u64,
    ) -> Option<Bug> {
        if !self.is_in_vaddr_range(address) || !self.is_in_vaddr_range(address + size) {
            trace!(
                "{}: buffer {:#x} - {:#x} out of virtual address range (0x0 - {:#x}) => computing reachability",
                instruction,
                address,
                address + size,
                self.state.memory.len() * 8,
            );

            self.is_running = false;

            Some(Bug::AccessToOutOfRangeAddress {
                info: RarityBugInfo {
                    inputs: self.concrete_inputs.clone(),
                    pc: self.state.pc,
                },
            })
        } else {
            None
        }
    }

    #[allow(clippy::unnecessary_wraps)]
    fn execute_lui(&mut self, utype: UType) -> Result<Option<Bug>, RaritySimulationError> {
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

    fn execute_divu_remu<Op>(
        &mut self,
        instruction: Instruction,
        rtype: RType,
        op: Op,
    ) -> Result<Option<Bug>, RaritySimulationError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        match self.state.regs[rtype.rs2() as usize] {
            Value::Concrete(divisor) if divisor == 0 => {
                trace!(
                    "{}: divisor == 0 -> compute reachability",
                    instruction_to_str(instruction)
                );

                Ok(Some(Bug::DivisionByZero {
                    info: RarityBugInfo {
                        inputs: self.concrete_inputs.clone(),
                        pc: self.state.pc,
                    },
                }))
            }
            _ => self.execute_rtype(instruction, rtype, op),
        }
    }

    fn execute_itype<Op>(
        &mut self,
        instruction: Instruction,
        itype: IType,
        op: Op,
    ) -> Result<Option<Bug>, RaritySimulationError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let rs1_value = self.state.regs[itype.rs1() as usize];
        let imm_value = Value::Concrete(itype.imm() as u64);

        self.execute_binary_op(instruction, rs1_value, imm_value, itype.rd(), op)
    }

    #[allow(clippy::unnecessary_wraps)]
    fn execute_rtype<Op>(
        &mut self,
        instruction: Instruction,
        rtype: RType,
        op: Op,
    ) -> Result<Option<Bug>, RaritySimulationError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let rs1_value = self.state.regs[rtype.rs1() as usize];
        let rs2_value = self.state.regs[rtype.rs2() as usize];

        self.execute_binary_op(instruction, rs1_value, rs2_value, rtype.rd(), op)
    }

    #[allow(clippy::unnecessary_wraps)]
    fn execute_binary_op<Op>(
        &mut self,
        instruction: Instruction,
        lhs: Value,
        rhs: Value,
        rd: Register,
        op: Op,
    ) -> Result<Option<Bug>, RaritySimulationError>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let result = match (lhs, rhs) {
            (Value::Concrete(v1), Value::Concrete(v2)) => Value::Concrete(op(v1, v2)),
            _ => {
                let bug = self.access_to_uninitialized_memory(instruction, lhs, rhs);

                trace!("could not find input assignment => exiting this context");

                self.is_running = false;

                return Ok(Some(bug));
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

    fn execute_brk(&mut self) -> Result<Option<Bug>, RaritySimulationError> {
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

    fn execute_read(&mut self) -> Result<Option<Bug>, RaritySimulationError> {
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

        let bug = self.check_for_valid_memory_range("read", buffer, size);
        if bug.is_some() {
            return Ok(bug);
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

    fn execute_write(
        &mut self,
        instruction: Instruction,
    ) -> Result<Option<Bug>, RaritySimulationError> {
        if !matches!(self.state.regs[Register::A0 as usize], Value::Concrete(1)) {
            return not_supported("can not handle other fd than stdout in write syscall");
        }

        let buffer = if let Value::Concrete(b) = self.state.regs[Register::A1 as usize] {
            b
        } else {
            return not_supported(
                "can not handle symbolic or uninitialized buffer address in write syscall",
            );
        };

        let size = if let Value::Concrete(s) = self.state.regs[Register::A2 as usize] {
            s
        } else {
            return not_supported("can not handle symbolic or uinitialized size in write syscall");
        };

        trace!("write: fd={} buffer={:#x} size={}", 1, buffer, size,);

        let bug = self.check_for_valid_memory_range("write", buffer, size);
        if bug.is_some() {
            return Ok(bug);
        }

        let size_of_u64 = size_of::<u64>() as u64;
        let start = buffer / size_of_u64;
        let bytes_to_read = size + buffer % size_of_u64;
        let words_to_read = (bytes_to_read + size_of_u64 - 1) / size_of_u64;

        for word_count in 0..words_to_read {
            if self.state.memory[(start + word_count) as usize] == Value::Uninitialized {
                trace!(
                    "write: access to uninitialized memory at {:#x} => computing reachability",
                    (start + word_count) * size_of_u64,
                );

                return Ok(Some(Bug::AccessToUnitializedMemory {
                    info: RarityBugInfo {
                        inputs: self.concrete_inputs.clone(),
                        pc: self.state.pc,
                    },
                    instruction,
                    operands: vec![],
                }));
            }
        }

        self.state.regs[Register::A0 as usize] = Value::Concrete(size);

        Ok(None)
    }

    #[allow(clippy::unnecessary_wraps)]
    fn execute_beq(&mut self, btype: BType) -> Result<Option<Bug>, RaritySimulationError> {
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

                let result = self.access_to_uninitialized_memory(Instruction::Beq(btype), v1, v2);

                trace!("access to uninitialized memory => exiting this context");

                Ok(Some(result))
            }
        }
    }

    fn execute_exit(&mut self) -> Result<Option<Bug>, RaritySimulationError> {
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
                            inputs: self.concrete_inputs.clone(),
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

    fn execute_ecall(
        &mut self,
        instruction: Instruction,
    ) -> Result<Option<Bug>, RaritySimulationError> {
        trace!("[{:#010x}] ecall", self.state.pc);

        let result = match self.state.regs[Register::A7 as usize] {
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Brk as u64) => {
                self.execute_brk()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Read as u64) => {
                self.execute_read()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Write as u64) => {
                self.execute_write(instruction)
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Exit as u64) => {
                self.execute_exit()
            }
            id => Err(RaritySimulationError::NotSupported(format!(
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
    ) -> Result<Option<Bug>, RaritySimulationError> {
        if let Value::Concrete(base_address) = self.state.regs[itype.rs1() as usize] {
            let immediate = itype.imm() as u64;

            let address = base_address.wrapping_add(immediate);

            let bug = self.check_for_valid_memory_address(instruction_to_str(instruction), address);

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
    ) -> Result<Option<Bug>, RaritySimulationError> {
        if let Value::Concrete(base_address) = self.state.regs[stype.rs1() as usize] {
            let immediate = stype.imm();

            let address = base_address.wrapping_add(immediate as u64);

            let bug = self.check_for_valid_memory_address(instruction_to_str(instruction), address);

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

    #[allow(clippy::unnecessary_wraps)]
    fn execute_jal(&mut self, jtype: JType) -> Result<Option<Bug>, RaritySimulationError> {
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

    fn execute_jalr(&mut self, itype: IType) -> Result<Option<Bug>, RaritySimulationError> {
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

fn not_supported(s: &str) -> Result<Option<Bug>, RaritySimulationError> {
    Err(RaritySimulationError::NotSupported(s.to_owned()))
}

#[derive(Default, Debug, Clone)]
pub struct RarityBugInfo {
    inputs: Vec<u64>,
    pc: u64,
}

impl BugInfo for RarityBugInfo {
    type Value = u64;
}

impl fmt::Display for RarityBugInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "concrete inputs read: {:?}", self.inputs)?;
        writeln!(f, "pc: {:#x}", self.pc)
    }
}

/// Calculates all state scores with a given scoring predicate
///
/// Using all states executed by the rarity simulation execution, this function constructs the
/// statistical counters and, based upon these, calculates the rarity score of each state.
///
/// The counters work on byte-granularity basis. For each byte contained by a state, 256 counters
/// are created, one for each possible state a byte can be in. All bytes of all states are iterated
/// and a corresponding counter is incremented depending on the byte's value.
/// This is done to count the ocurrences of distinct values for each byte. The smaller a counter
/// value is, the rarer the value of this specific counter is for a specific byte.
///
/// The function then determines the the counter values that are relevant for rarity calculation,
/// for each state, that is, for each byte it appends the value of the counter relevant to the byte
/// and the byte's value.
///
/// The list of relevant counter values is passed to the scoring function in order to determine the
/// rarity score of each state.
///
/// # Arguments
/// * states: A list of states.
/// * score: A function taking the amount of states and relevant statistical counter values and returning a score
fn compute_scores<F>(states: &[&State], score: F) -> Vec<f64>
where
    F: Fn(usize, &[Counter]) -> f64,
{
    let counter_addresses: Vec<Vec<Address>> = states
        .iter()
        .map(|s| compute_counter_addresses(&s))
        .collect();

    // create global counters for all states
    let mut overall_counts = HashMap::<Address, Counter>::new();

    counter_addresses
        .iter()
        .flatten()
        .for_each(|address| count_address(&mut overall_counts, *address));

    // create counters per state based on overall counts
    let n = states.len();

    counter_addresses
        .iter()
        .map(|addresses| {
            addresses
                .iter()
                .map(|address| {
                    *overall_counts
                        .get(address)
                        .expect("cound should be available")
                })
                .collect_vec()
        })
        .map(|addresses| score(n, &addresses[..]))
        .collect()
}

fn count_address(scores: &mut HashMap<Address, Counter>, addr: Address) {
    if let Some(entry) = scores.get_mut(&addr) {
        *entry += 1;
    } else {
        scores.insert(addr, 1);
    }
}

/// Based on a state, generates an iterator that contains
/// matching counter `addresses` for each byte.
///
/// The counter address is a combination of the byte's address and the value of that
/// address in the state.
///
/// Each byte assumes one of 256 (2^8) values.
/// Thus, each distinct byte i of the state has has 256 different addresses: (i*256)..((i*256) + 255)
/// That is, each byte is `expanded` to 256 addresses.
///
/// The first 8 bytes are represented by the program counter, in the CPU's native byte ordering
/// Next, 32 64-bit registers are represented.
/// Then, all touched memory regions follow.
///
/// For each byte i, only one of its 256 different addresses may occur (because a byte can only
/// assume one state at a time)
fn compute_counter_addresses(state: &State) -> Vec<Address> {
    fn offset_for_word(idx: u64) -> u64 {
        idx * BYTES_PER_WORD * NUMBER_OF_BYTE_VALUES
    }

    let mut addresses = Vec::new();

    compute_counter_addresses_for_word(0, state.pc, &mut addresses);

    compute_counter_addresses_for_iter(offset_for_word(1), state.regs.iter(), &mut addresses);

    compute_counter_addresses_for_iter(offset_for_word(33), state.memory.iter(), &mut addresses);

    addresses
}

/// Appends relevant statistic counter addresses from an iterator
///
/// Iterates over a collection of [`Value`]s and appends them to the relevant address list if they
/// contain a concrete value.
///
/// # Arguments
/// * offset: The statistic counter address offset
/// * iter: The iterator
/// * addresses: The list where relevant addresses shall be appended to
///
/// # See
/// * [`compute_counter_addresses_for_word`]
fn compute_counter_addresses_for_iter<'a, Iter>(
    offset: u64,
    iter: Iter,
    addresses: &mut Vec<Address>,
) where
    Iter: Iterator<Item = &'a Value>,
{
    iter.enumerate()
        .filter_map(|(idx, v)| match v {
            Value::Concrete(w) => Some((idx, w)),
            _ => None,
        })
        .for_each(|(idx, word)| {
            compute_counter_addresses_for_word(
                offset + idx as u64 * NUMBER_OF_BYTE_VALUES,
                *word,
                addresses,
            );
        });
}

/// Appends to a counter address list
///
/// Splits a 64-bit word into bytes (using the host machine's endianess) and appennds the relevant
/// counter addresses, depending on their respective values.
///
/// # Arguments
/// * offset:
/// * word: The word that s
/// * addresses: The list where relevant addresses shall be appended to
fn compute_counter_addresses_for_word(offset: u64, word: u64, addresses: &mut Vec<u64>) {
    u64::to_ne_bytes(word)
        .iter()
        .cloned()
        .enumerate()
        .for_each(|(byte_idx, byte_value)| {
            let byte_address = BYTES_PER_WORD * byte_idx as u64;
            let address = offset + byte_address * NUMBER_OF_BYTE_VALUES + byte_value as u64;
            addresses.push(address);
        });
}

/// Generates a random value limited by an upper bound
///
/// Returns a random value between 0 inclusive and `len` exclusively by using the modulo operator
fn random_index(len: usize) -> usize {
    rand::random::<usize>() % len
}

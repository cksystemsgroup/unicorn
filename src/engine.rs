use crate::{
    bitvec::BitVector,
    boolector::Boolector,
    cfg::build_cfg_from_file,
    exploration_strategy::{ExplorationStrategy, ShortestPathStrategy},
    solver::{Assignment, MonsterSolver, Solver},
    symbolic_state::{Query, SymbolId, SymbolicState},
    z3::Z3,
};
use anyhow::Result;
use byteorder::{ByteOrder, LittleEndian};
use bytesize::ByteSize;
use log::{debug, info, trace};
use riscu::{decode, types::*, Instruction, Program, ProgramSegment, Register};
use std::{cell::RefCell, collections::HashMap, fmt, mem::size_of, path::Path, rc::Rc};

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

// TODO: What should the engine return as result?
pub fn execute<P>(input: P, with: Backend) -> Result<()>
where
    P: AsRef<Path>,
{
    let ((graph, _), program) = build_cfg_from_file(input)?;

    let mut strategy = ShortestPathStrategy::new(&graph, program.code.address);

    match with {
        Backend::Monster => {
            let solver = Rc::new(RefCell::new(MonsterSolver::new()));
            let state = Box::new(SymbolicState::new(solver));

            let mut executor = Engine::new(ByteSize::mib(1), &program, &mut strategy, state);

            executor.run()
        }
        Backend::Boolector => {
            let solver = Rc::new(RefCell::new(Boolector::new()));
            let state = Box::new(SymbolicState::new(solver));

            let mut executor = Engine::new(ByteSize::mib(1), &program, &mut strategy, state);

            executor.run()
        }
        Backend::Z3 => {
            let solver = Rc::new(RefCell::new(Z3::new()));
            let state = Box::new(SymbolicState::new(solver));

            let mut executor = Engine::new(ByteSize::mib(1), &program, &mut strategy, state);

            executor.run()
        }
    }
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
    strategy: &'a mut E,
    is_exited: bool,
}

impl<'a, E, S> Engine<'a, E, S>
where
    E: ExplorationStrategy,
    S: Solver,
{
    // creates a machine state with a specific memory size
    pub fn new(
        memory_size: ByteSize,
        program: &Program,
        strategy: &'a mut E,
        symbolic_state: Box<SymbolicState<S>>,
    ) -> Self {
        let mut regs = [Value::Concrete(0); 32];
        let mut memory = vec![Value::Uninitialized; memory_size.as_u64() as usize / 8];

        let sp = memory_size.as_u64() - 8;
        regs[Register::Sp as usize] = Value::Concrete(sp);

        // TODO: Init main function arguments
        let argc = 0;
        memory[sp as usize / size_of::<u64>()] = Value::Concrete(argc);

        Self::load_segment(&mut memory, &program.code);
        Self::load_segment(&mut memory, &program.data);

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
            is_exited: false,
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

    pub fn run(&mut self) -> Result<()> {
        while !self.is_exited {
            let word = self.fetch();

            let instr = decode(word)?;

            self.execute(instr)?;
        }

        Ok(())
    }

    fn handle_solver_result(&self, reason: &str, solver_result: Option<Assignment<BitVector>>) {
        if let Some(assignment) = solver_result {
            let printable_assignments = self.symbolic_state.get_input_assignments(&assignment);

            info!("{}: found input assignment", reason);
            print_assignment(&printable_assignments);

            info!("exiting execution engine");
            std::process::exit(0);
        }
    }

    fn check_for_uninitialized_memory(&mut self, instruction: &str, v1: Value, v2: Value) {
        trace!("{}: {}, {} => computing reachability", instruction, v1, v2);

        let solver_result = self.symbolic_state.execute_query(Query::Reachable);

        self.handle_solver_result(
            format!("access to unintialized memory in {}", instruction).as_str(),
            solver_result,
        );
    }

    fn check_for_valid_memory_address(&mut self, instruction: &str, address: u64) -> bool {
        let is_alignment_ok = address % size_of::<u64>() as u64 == 0;
        let is_in_vadd_range = address as usize / size_of::<u64>() < self.memory.len();

        if !is_alignment_ok {
            trace!(
                "{}: address {:#x} is not double word aligned => computing reachability",
                instruction,
                address
            );

            let solver_result = self.symbolic_state.execute_query(Query::Reachable);

            self.handle_solver_result(
                format!(
                    "address {:#x} not double word aligned in {}",
                    address, instruction
                )
                .as_str(),
                solver_result,
            );

            trace!(
                "{}: could not find valid assignment => exiting context",
                instruction
            );

            self.is_exited = true;

            false
        } else if !is_in_vadd_range {
            trace!(
                "{}: address {:#x} out of virtual address range (0x0 - {:#x}) => computing reachability",
                instruction,
                address,
                self.memory.len() * 8,
            );

            let solver_result = self.symbolic_state.execute_query(Query::Reachable);

            self.handle_solver_result(
                format!(
                    "address {:#x} out of virtual address range (0x0 - {:#x}) in {}",
                    address,
                    self.memory.len() * 8,
                    instruction,
                )
                .as_str(),
                solver_result,
            );

            trace!(
                "{}: could not find valid assignment => exiting context",
                instruction
            );

            self.is_exited = true;

            false
        } else {
            true
        }
    }

    fn execute_lui(&mut self, utype: UType) {
        let immediate = u64::from(utype.imm());

        let result = Value::Concrete(immediate);

        trace!(
            "[{:#010x}] {}: {:?} <- {}",
            self.pc,
            instruction_to_str(Instruction::Lui(utype)),
            utype.rd(),
            result,
        );

        if utype.rd() != Register::Zero {
            self.regs[utype.rd() as usize] = result;
        }

        self.pc += 4;
    }

    fn execute_divu(&mut self, instruction: Instruction, rtype: RType) {
        match self.regs[rtype.rs2() as usize] {
            Value::Symbolic(divisor) => {
                // TODO: fix this possible exit point when refactoring engine interface
                trace!("divu: symbolic divisor -> find input for divisor == 0");

                let solver_result = self
                    .symbolic_state
                    .execute_query(Query::Equals((divisor, 0)));

                self.handle_solver_result("division by zero in DIVU", solver_result);
            }
            Value::Concrete(divisor) if divisor == 0 => {
                // TODO: fix this possible exit point when refactoring engine interface
                trace!("divu: divisor == 0 -> compute reachability");

                let solver_result = self.symbolic_state.execute_query(Query::Reachable);

                self.handle_solver_result("division by zero in DIVU", solver_result);
            }
            _ => {}
        }

        self.execute_rtype(instruction, rtype, u64::wrapping_div);
    }

    fn execute_itype<Op>(&mut self, instruction: Instruction, itype: IType, op: Op)
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let rs1_value = self.regs[itype.rs1() as usize];
        let imm_value = Value::Concrete(itype.imm() as u64);

        let result = self.execute_binary_op(instruction, rs1_value, imm_value, op);

        trace!(
            "[{:#010x}] {}: {}, {} |- {:?} <- {}",
            self.pc - 4,
            instruction_to_str(instruction),
            rs1_value,
            imm_value,
            itype.rd(),
            result,
        );

        if itype.rd() != Register::Zero {
            self.regs[itype.rd() as usize] = result;
        }
    }

    fn execute_rtype<Op>(&mut self, instruction: Instruction, rtype: RType, op: Op)
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        let rs1_value = self.regs[rtype.rs1() as usize];
        let rs2_value = self.regs[rtype.rs2() as usize];

        let result = self.execute_binary_op(instruction, rs1_value, rs2_value, op);

        trace!(
            "[{:#010x}] {}:  {}, {} |- {:?} <- {}",
            self.pc - 4,
            instruction_to_str(instruction),
            rs1_value,
            rs2_value,
            rtype.rd(),
            result,
        );

        if rtype.rd() != Register::Zero {
            self.regs[rtype.rd() as usize] = result;
        }
    }

    fn execute_binary_op<Op>(
        &mut self,
        instruction: Instruction,
        lhs: Value,
        rhs: Value,
        op: Op,
    ) -> Value
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        self.pc += 4;

        match (lhs, rhs) {
            (Value::Concrete(v1), Value::Concrete(v2)) => Value::Concrete(op(v1, v2)),
            (Value::Symbolic(v1), Value::Concrete(v2)) => {
                let v2 = self.symbolic_state.create_const(v2);
                Value::Symbolic(self.symbolic_state.create_operator(instruction, v1, v2))
            }
            (Value::Concrete(v1), Value::Symbolic(v2)) => {
                let v1 = self.symbolic_state.create_const(v1);
                Value::Symbolic(self.symbolic_state.create_operator(instruction, v1, v2))
            }
            (Value::Symbolic(v1), Value::Symbolic(v2)) => {
                Value::Symbolic(self.symbolic_state.create_operator(instruction, v1, v2))
            }
            (v1, v2) => {
                // TODO: fix this possible exit point when refactoring engine interface
                self.check_for_uninitialized_memory(instruction_to_str(instruction), v1, v2);

                trace!("could not find input assignment => exeting this context");

                self.is_exited = true;

                Value::Uninitialized
            }
        }
    }

    fn execute_brk(&mut self) {
        if let Value::Concrete(new_program_break) = self.regs[Register::A0 as usize] {
            // TODO: handle cases where program break can not be modified
            let old_program_break = self.program_break;

            if new_program_break < self.program_break {
                self.regs[Register::A0 as usize] = Value::Concrete(self.program_break);
            } else {
                self.program_break = new_program_break;
            }

            trace!(
                "brk: old={:#x} new={:#x}",
                old_program_break,
                new_program_break
            );
        } else {
            unimplemented!("can not handle symbolic or uninitialized program break")
        }
    }

    fn execute_read(&mut self) {
        if let Value::Concrete(fd) = self.regs[Register::A0 as usize] {
            if fd == 0 {
                if let Value::Concrete(buffer) = self.regs[Register::A1 as usize] {
                    if let Value::Concrete(size) = self.regs[Register::A2 as usize] {
                        // TODO: round up to word width.. not the best idea, right???

                        let to_add = if size % 8 == 0 { 0 } else { 8 - (size % 8) };
                        let words_read = (size + to_add) / 8;

                        for i in 0..words_read {
                            let name = format!("read({}, {}, {})", 0, buffer, size);

                            let node_idx = self.symbolic_state.create_input(&name);

                            self.memory[((buffer / 8) + i) as usize] = Value::Symbolic(node_idx);
                        }

                        trace!(
                            "read: fd={} buffer={:#x} size={} -> {} symbolic double words read",
                            fd,
                            buffer,
                            size,
                            words_read,
                        );
                    } else {
                        unimplemented!(
                            "can not handle symbolic or uinitialized size in read syscall"
                        )
                    }
                } else {
                    unimplemented!(
                        "can not handle symbolic or uninitialized buffer address in read syscall"
                    )
                }
            } else {
                unimplemented!("can not handle other fd than stdin in read syscall")
            }
        } else {
            unimplemented!("can not handle symbolic or uninitialized fd in read syscall")
        }
    }

    fn execute_beq_branches(
        &mut self,
        true_branch: u64,
        false_branch: u64,
        lhs: SymbolId,
        rhs: SymbolId,
    ) -> Result<()> {
        let memory_snapshot = self.memory.clone();
        let regs_snapshot = self.regs;
        let graph_snapshot = Box::new((*self.symbolic_state).clone());
        let brk_snapshot = self.program_break;

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
        self.run()?;

        self.is_exited = false;

        self.memory = memory_snapshot;
        self.regs = regs_snapshot;
        self.symbolic_state = graph_snapshot;
        self.program_break = brk_snapshot;

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

        Ok(())
    }

    fn execute_beq(&mut self, btype: BType) -> Result<()> {
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
            (v1, v2) => {
                // TODO: fix this possible exit point when refactoring engine interface
                self.check_for_uninitialized_memory("beq", v1, v2);

                trace!("could not find input assignment => exeting this context");

                self.is_exited = true;

                Ok(())
            }
        }
    }

    fn execute_exit(&mut self) {
        match self.regs[Register::A0 as usize] {
            Value::Symbolic(exit_code) => {
                trace!("exit: symbolic code -> find input for exit_code != 0");

                // TODO: fix this possible exit point when refactoring engine interface
                let result = self
                    .symbolic_state
                    .execute_query(Query::NotEquals((exit_code, 0)));

                self.handle_solver_result("exit_code > 0", result);
            }
            Value::Concrete(exit_code) => {
                if exit_code > 0 {
                    trace!(
                        "exit: with code {} -> find input to satisfy path condition",
                        exit_code
                    );

                    // TODO: fix this possible exit point when refactoring engine interface
                    let result = self.symbolic_state.execute_query(Query::Reachable);

                    self.handle_solver_result("exit_code > 0", result);
                } else {
                    trace!("exiting context with exit_code 0");
                }
            }
            _ => unimplemented!("exit only implemented for symbolic exit codes"),
        }

        self.is_exited = true;
    }

    fn execute_ecall(&mut self) {
        trace!("[{:#010x}] ecall", self.pc,);

        match self.regs[Register::A7 as usize] {
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Brk as u64) => {
                self.execute_brk()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Read as u64) => {
                self.execute_read()
            }
            Value::Concrete(syscall_id) if syscall_id == (SyscallId::Exit as u64) => {
                self.execute_exit()
            }
            Value::Concrete(x) => unimplemented!("this syscall ({}) is not implemented yet", x),
            Value::Uninitialized => unimplemented!("ecall with uninitialized syscall id"),
            Value::Symbolic(_) => unimplemented!("ecall with symbolic syscall id not implemented"),
        }

        self.pc += 4;
    }

    fn execute_ld(&mut self, instruction: Instruction, itype: IType) {
        if let Value::Concrete(base_address) = self.regs[itype.rs1() as usize] {
            let immediate = itype.imm() as u64;

            let address = base_address.wrapping_add(immediate);

            // TODO: fix this possible exit point when refactoring engine interface
            if self.check_for_valid_memory_address(instruction_to_str(instruction), address) {
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

                if itype.rd() != Register::Zero {
                    self.regs[itype.rd() as usize] = value;
                }
            }
        } else {
            panic!("can not handle symbolic addresses in LD")
        }

        self.pc += 4;
    }

    fn execute_sd(&mut self, instruction: Instruction, stype: SType) {
        if let Value::Concrete(base_address) = self.regs[stype.rs1() as usize] {
            let immediate = stype.imm();

            let address = base_address.wrapping_add(immediate as u64);

            // TODO: fix this possible exit point when refactoring engine interface
            if self.check_for_valid_memory_address(instruction_to_str(instruction), address) {
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
            }
        } else {
            panic!("can not handle symbolic addresses in SD")
        }

        self.pc += 4;
    }

    fn execute_jal(&mut self, jtype: JType) {
        let link = self.pc + 4;

        let new_pc = self.pc.wrapping_add(jtype.imm() as u64);

        trace!(
            "[{:#010x}] jal: pc <- {:#x}, {:?} <- {:#x}",
            self.pc,
            new_pc,
            jtype.rd(),
            link,
        );

        self.pc = new_pc;

        if jtype.rd() != Register::Zero {
            self.regs[jtype.rd() as usize] = Value::Concrete(link);
        }
    }

    fn execute_jalr(&mut self, itype: IType) {
        let link = self.pc + 4;

        if let Value::Concrete(dest) = self.regs[itype.rs1() as usize] {
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

            self.pc = new_pc;
        } else {
            panic!("can only handle concrete addresses in JALR")
        }

        if itype.rd() != Register::Zero {
            self.regs[itype.rd() as usize] = Value::Concrete(link);
        }
    }

    fn fetch(&self) -> u32 {
        if let Value::Concrete(dword) = self.memory[(self.pc / 8) as usize] {
            if self.pc % 8 == 0 {
                dword as u32
            } else {
                (dword >> 32) as u32
            }
        } else {
            panic!("tried to fetch none concrete instruction")
        }
    }

    fn execute(&mut self, instruction: Instruction) -> Result<()> {
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
            Instruction::Beq(btype) => self.execute_beq(btype)?,
        }

        Ok(())
    }
}

fn print_assignment(assignment: &HashMap<String, BitVector>) {
    assignment.iter().for_each(|(name, value)| {
        info!("{} = {:?} ({})", name, value, value.0);
    });
}

const fn instruction_to_str(i: Instruction) -> &'static str {
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

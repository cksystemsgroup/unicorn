use crate::elf::ElfMetadata;
use crate::iterator::ForEachUntilSome;
use byteorder::{ByteOrder, LittleEndian};
use core::fmt;
pub use petgraph::graph::NodeIndex;
use petgraph::Graph;
use riscv_decode::types::{BType, IType, RType, SType, UType};
use riscv_decode::{Instruction, Register};

pub type Formula = Graph<Node, ArgumentSide>;

pub static REG_SP: usize = 2;
pub static REG_A0: usize = 10;
pub static REG_A1: usize = 11;
pub static REG_A2: usize = 12;
pub static REG_A7: usize = 17;

#[allow(dead_code)]
pub enum SyscallId {
    Exit = 93,
    Read = 63,
    Write = 64,
    Openat = 56,
    Brk = 214,
}

pub fn instruction_to_str(i: Instruction) -> &'static str {
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
        _ => "unknown",
    }
}

#[derive(Clone, Debug, Copy, Eq, Hash, PartialEq)]
pub enum ArgumentSide {
    Lhs,
    Rhs,
}

impl ArgumentSide {
    #[allow(dead_code)]
    pub fn other(&self) -> Self {
        match self {
            ArgumentSide::Lhs => ArgumentSide::Rhs,
            ArgumentSide::Rhs => ArgumentSide::Lhs,
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct Instr {
    // These instructions are part of the formula graph
    // IE = input edge
    // OE = output edge
    // Lui(utype) -> 0 IE / 1 OE
    // Addi(itype) -> 1 IE / 1 OE
    // Add(rtype) -> 2 IE / 1 OE
    // Sub(rtype) -> 2 IE / 1 OE
    // Mul(rtype) -> 2 IE / 1 OE
    // Divu(rtype) -> 2 IE / 1 OE
    // Remu(rtype) -> 2 IE / 1 OE
    // Sltu(rtype) -> 2 IE / 1 OE
    pub instruction: Instruction,
}

impl Instr {
    pub fn new(instruction: Instruction) -> Self {
        Self { instruction }
    }
}

impl fmt::Debug for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.instruction)
    }
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct Const {
    // can have multiple output edges, but no input edge
    pub value: u64,
}

impl Const {
    pub fn new(value: u64) -> Self {
        Self { value }
    }
}

impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub struct Input {
    // can have multiple output edges, but no input edge
    pub name: String,
}

impl Input {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl fmt::Debug for Input {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BooleanFunction {
    NotEqual,
    Equals,
    GreaterThan,
}

impl fmt::Display for BooleanFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanFunction::GreaterThan => write!(f, "Greater Than"),
            BooleanFunction::Equals => write!(f, "Equal"),
            BooleanFunction::NotEqual => write!(f, "Not Equal"),
        }
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub struct Constraint {
    // has 1 input edge only and 0 output edges
    pub name: String,
    pub op: BooleanFunction,
}

impl Constraint {
    pub fn new(name: String, op: BooleanFunction) -> Self {
        Self { name, op }
    }
}

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}, {}", self.name, self.op)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Node {
    Instruction(Instr),
    Constant(Const),
    Input(Input),
    Constraint(Constraint),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Value {
    Concrete(u64),
    Symbolic(NodeIndex),
    Uninitialized,
}

struct DataFlowGraphBuilder<'a> {
    graph: Formula,
    path: &'a [Instruction],
    program_break: u64,
    regs: [Value; 32],
    memory: Vec<Value>,
    branch_decisions: Vec<bool>,
}

pub enum ExecutionResult {
    PotentialError(NodeIndex),
    PathUnsat,
}

impl<'a> DataFlowGraphBuilder<'a> {
    // creates a machine state with a specific memory size
    fn new(
        memory_size: usize,
        path: &'a [Instruction],
        data_segment: &[u8],
        elf_metadata: &ElfMetadata,
        branch_decisions: Vec<bool>,
    ) -> Self {
        let mut regs = [Value::Concrete(0); 32];
        let mut memory = vec![Value::Uninitialized; memory_size / 8];

        regs[REG_SP] = Value::Concrete(memory_size as u64 - 8);

        println!(
            "data_segment.len(): {}   entry_address:  {}",
            data_segment.len(),
            elf_metadata.entry_address
        );

        let start = ((elf_metadata.entry_address + elf_metadata.code_length) / 8) as usize;
        let end = start + (data_segment.len() / 8);

        data_segment
            .chunks(8)
            .map(LittleEndian::read_u64)
            .zip(start..end)
            .for_each(|(x, i)| memory[i] = Value::Concrete(x));

        Self {
            graph: Formula::new(),
            program_break: elf_metadata.entry_address + (data_segment.len() as u64),
            path,
            regs,
            memory,
            branch_decisions,
        }
    }

    fn create_const_node(&mut self, value: u64) -> NodeIndex {
        let constant = Node::Constant(Const::new(value));

        self.graph.add_node(constant)
    }

    fn symbolic_op(&mut self, lhs: NodeIndex, rhs: NodeIndex, result: NodeIndex) -> Value {
        self.graph.add_edge(lhs, result, ArgumentSide::Lhs);
        self.graph.add_edge(rhs, result, ArgumentSide::Rhs);

        Value::Symbolic(result)
    }

    fn execute_lui(&mut self, utype: UType) -> Option<ExecutionResult> {
        if utype.rd() == Register::Zero {
            return None;
        }

        let immediate = u64::from(utype.imm());

        let result = Value::Concrete(immediate);

        println!(
            "{}  imm: {:?} -> rd: {:?}",
            instruction_to_str(Instruction::Lui(utype)),
            immediate as i64,
            result,
        );

        self.regs[utype.rd() as usize] = result;

        None
    }

    fn execute_itype<Op>(
        &mut self,
        instruction: Instruction,
        itype: IType,
        op: Op,
    ) -> Option<ExecutionResult>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        if itype.rd() == Register::Zero {
            return None;
        }

        let rs1_value = self.regs[itype.rs1() as usize];

        let result = self.execute_binary_op(
            instruction,
            rs1_value,
            Value::Concrete(itype.imm() as u64),
            op,
        );

        println!(
            "{}  rs1: {:?} imm: {:?} -> rd: {:?}",
            instruction_to_str(instruction),
            rs1_value,
            itype.imm() as i64,
            result,
        );

        self.regs[itype.rd() as usize] = result;

        None
    }

    fn execute_rtype<Op>(
        &mut self,
        instruction: Instruction,
        rtype: RType,
        op: Op,
    ) -> Option<ExecutionResult>
    where
        Op: FnOnce(u64, u64) -> u64,
    {
        if rtype.rd() == Register::Zero {
            return None;
        }

        let rs1_value = self.regs[rtype.rs1() as usize];
        let rs2_value = self.regs[rtype.rs2() as usize];

        let result = self.execute_binary_op(instruction, rs1_value, rs2_value, op);

        println!(
            "{}  rs1: {:?} rs2: {:?} -> rd: {:?}",
            instruction_to_str(instruction),
            rs1_value,
            rs2_value,
            result,
        );

        self.regs[rtype.rd() as usize] = result;

        None
    }

    fn create_result_node(&mut self, instruction: Instruction) -> NodeIndex {
        let node = Node::Instruction(Instr::new(instruction));

        self.graph.add_node(node)
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
        match (lhs, rhs) {
            (Value::Concrete(v1), Value::Concrete(v2)) => Value::Concrete(op(v1, v2)),
            (Value::Symbolic(v1), Value::Concrete(v2)) => {
                let node = self.create_const_node(v2);
                let res = self.create_result_node(instruction);
                self.symbolic_op(v1, node, res)
            }
            (Value::Concrete(v1), Value::Symbolic(v2)) => {
                let node = self.create_const_node(v1);
                let res = self.create_result_node(instruction);
                self.symbolic_op(node, v2, res)
            }
            (Value::Symbolic(v1), Value::Symbolic(v2)) => {
                let res = self.create_result_node(instruction);
                self.symbolic_op(v1, v2, res)
            }
            // TODO: generate exit node here
            _ => panic!("access to unitialized memory"),
        }
    }

    pub fn generate_graph(&mut self) -> Option<(Formula, ExecutionResult)> {
        if let Some(result) = self
            .path
            .iter()
            .for_each_until_some(|instr| self.execute(*instr))
        {
            Some((self.graph.clone(), result))
        } else {
            None
        }
    }

    fn execute_brk(&mut self) -> Option<ExecutionResult> {
        if let Value::Concrete(new_program_break) = self.regs[REG_A0] {
            // TODO: handle cases where program break can not be modified
            if new_program_break < self.program_break {
                self.regs[REG_A0] = Value::Concrete(self.program_break);
            } else {
                self.program_break = new_program_break;
            }
            println!("new program break: {}", new_program_break);
        } else {
            unimplemented!("can not handle symbolic or uninitialized program break")
        }
        None
    }

    fn execute_read(&mut self) -> Option<ExecutionResult> {
        // TODO: ignore FD??
        if let Value::Concrete(buffer) = self.regs[REG_A1] {
            if let Value::Concrete(size) = self.regs[REG_A2] {
                // assert!(
                //     size % 8 == 0,
                //     "can only handle read syscalls with word width"
                // );
                // TODO: round up to word width.. not the best idea, right???
                let to_add = 8 - (size % 8);
                let words_read = (size + to_add) / 8;

                for i in 0..words_read {
                    let name = format!("read({}, {}, {})", 0, buffer, size);
                    let node = Node::Input(Input::new(name));
                    let node_idx = self.graph.add_node(node);
                    self.memory[((buffer / 8) + i) as usize] = Value::Symbolic(node_idx);
                }
            } else {
                unimplemented!("can not handle symbolic or uinitialized size in read syscall")
            }
        } else {
            unimplemented!(
                "can not handle symbolic or uninitialized buffer address in read syscall"
            )
        }
        None
    }

    fn execute_beq(&mut self, btype: BType) -> Option<ExecutionResult> {
        fn create_constraint_node(decision: bool, graph: &mut Formula) -> NodeIndex {
            let node = Node::Constraint(Constraint::new(
                "beq".to_string(),
                if decision {
                    BooleanFunction::Equals
                } else {
                    BooleanFunction::NotEqual
                },
            ));

            graph.add_node(node)
        }

        let lhs = self.regs[btype.rs1() as usize];
        let rhs = self.regs[btype.rs2() as usize];
        let decision = self.branch_decisions.remove(0);

        println!("{:?}", lhs);
        println!("{:?}", rhs);

        match (lhs, rhs) {
            (Value::Concrete(v1), Value::Concrete(v2)) => {
                let actual_decision = v1 == v2;

                if decision != actual_decision {
                    return Some(ExecutionResult::PathUnsat);
                }
            }
            (Value::Symbolic(v1), Value::Concrete(v2)) => {
                let node_idx = create_constraint_node(decision, &mut self.graph);
                let const_node = self.create_const_node(v2);
                self.graph.add_edge(v1, node_idx, ArgumentSide::Lhs);
                self.graph.add_edge(const_node, node_idx, ArgumentSide::Rhs);
            }
            (Value::Concrete(v1), Value::Symbolic(v2)) => {
                let node_idx = create_constraint_node(decision, &mut self.graph);
                let const_node = self.create_const_node(v1);
                self.graph.add_edge(const_node, node_idx, ArgumentSide::Lhs);
                self.graph.add_edge(v2, node_idx, ArgumentSide::Rhs);
            }
            (Value::Symbolic(v1), Value::Symbolic(v2)) => {
                let node_idx = create_constraint_node(decision, &mut self.graph);
                self.graph.add_edge(v1, node_idx, ArgumentSide::Lhs);
                self.graph.add_edge(v2, node_idx, ArgumentSide::Rhs);
            }
            _ => panic!("access to uninitialized memory"),
        }
        None
    }

    fn execute_exit(&mut self) -> Option<ExecutionResult> {
        if let Value::Symbolic(exit_code) = self.regs[REG_A0] {
            let const_node = Node::Constant(Const::new(1));
            let const_node_idx = self.graph.add_node(const_node);

            let root = Node::Constraint(Constraint::new(
                String::from("exit_code"),
                BooleanFunction::Equals,
            ));
            let root_idx = self.graph.add_node(root);

            self.graph.add_edge(exit_code, root_idx, ArgumentSide::Lhs);
            self.graph
                .add_edge(const_node_idx, root_idx, ArgumentSide::Rhs);

            Some(ExecutionResult::PotentialError(root_idx))
        } else {
            unimplemented!("exit only implemented for symbolic exit codes")
        }
    }

    fn execute_ecall(&mut self) -> Option<ExecutionResult> {
        match self.regs[REG_A7] {
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
    }

    fn execute_load(&mut self, instruction: Instruction, itype: IType) -> Option<ExecutionResult> {
        if itype.rd() != Register::Zero {
            if let Value::Concrete(base_address) = self.regs[itype.rs1() as usize] {
                let immediate = itype.imm() as u64;

                let address = base_address.wrapping_add(immediate);

                let value = self.memory[(address / 8) as usize];

                println!(
                    "{} rs1: {:?} imm: {} -> rd: {:?}",
                    instruction_to_str(instruction),
                    self.regs[itype.rs1() as usize],
                    immediate as i64,
                    value,
                );

                self.regs[itype.rd() as usize] = value;
            } else {
                unimplemented!("can not handle symbolic addresses in LD")
            }
        }

        None
    }

    fn execute_store(&mut self, instruction: Instruction, stype: SType) -> Option<ExecutionResult> {
        if let Value::Concrete(base_address) = self.regs[stype.rs1() as usize] {
            let immediate = stype.imm();

            let address = base_address.wrapping_add(immediate as u64);

            let value = self.regs[stype.rs2() as usize];

            println!(
                "{}  immediate: {:?} rs2: {:?} rs1: {:?} -> ",
                instruction_to_str(instruction),
                immediate as i64,
                self.regs[stype.rs1() as usize],
                value,
            );

            self.memory[(address / 8) as usize] = value;
        } else {
            unimplemented!("can not handle symbolic addresses in SD")
        }

        None
    }

    fn execute(&mut self, instruction: Instruction) -> Option<ExecutionResult> {
        match instruction {
            Instruction::Ecall(_) => self.execute_ecall(),
            Instruction::Lui(utype) => self.execute_lui(utype),
            Instruction::Addi(itype) => self.execute_itype(instruction, itype, u64::wrapping_add),
            Instruction::Add(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_add),
            Instruction::Sub(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_sub),
            Instruction::Mul(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_mul),
            // TODO: Implement exit for DIVU
            Instruction::Divu(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_div),
            Instruction::Remu(rtype) => self.execute_rtype(instruction, rtype, u64::wrapping_rem),
            Instruction::Sltu(rtype) => {
                self.execute_rtype(instruction, rtype, |l, r| if l < r { 1 } else { 0 })
            }
            Instruction::Ld(itype) => self.execute_load(instruction, itype),
            Instruction::Sd(stype) => self.execute_store(instruction, stype),
            Instruction::Jal(jtype) => {
                if jtype.rd() != Register::Zero {
                    self.regs[jtype.rd() as usize] = Value::Concrete(0);
                }
                None
            }
            Instruction::Jalr(itype) => {
                if itype.rd() != Register::Zero {
                    self.regs[itype.rd() as usize] = Value::Concrete(0);
                }
                None
            }
            Instruction::Beq(btype) => self.execute_beq(btype),
            _ => unimplemented!("can not handle this instruction"),
        }
    }
}

pub fn sign_extend(n: u32, b: u32) -> u64 {
    // assert: 0 <= n <= 2^b
    // assert: 0 < b < CPUBITWIDTH
    let n = u64::from(n);

    if n < 2_u64.pow(b - 1) {
        n
    } else {
        n.wrapping_sub(2_u64.pow(b))
    }
}

#[allow(dead_code)]
pub fn sign_extend_utype(imm: u32) -> u64 {
    sign_extend(imm, 20)
}

pub fn sign_extend_jtype(imm: u32) -> u64 {
    sign_extend(imm, 21)
}

pub fn sign_extend_itype_stype(imm: u32) -> u64 {
    sign_extend(imm, 12)
}

pub fn sign_extend_btype(imm: u32) -> u64 {
    sign_extend(imm, 13)
}

#[allow(dead_code)]
pub fn build_dataflow_graph(
    path: &[Instruction],
    data_segment: &[u8],
    elf_metadata: &ElfMetadata,
    branch_decision: Vec<bool>,
) -> Option<(Formula, ExecutionResult)> {
    DataFlowGraphBuilder::new(
        1_000_000,
        path,
        data_segment,
        &elf_metadata,
        branch_decision,
    )
    .generate_graph()
}

// TODO: need to load data segment  => then write test
#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate_path::create_candidate_paths;
    use crate::cfg::build_cfg_from_file;
    use petgraph::dot::Dot;
    use serial_test::serial;
    use std::env::current_dir;
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::Path;
    use std::process::Command;

    // TODO: write a unit test without dependency on selfie and external files
    #[test]
    #[serial]
    fn can_build_formula() {
        let cd = String::from(current_dir().unwrap().to_str().unwrap());

        // generate RISC-U binary with Selfie
        let _ = Command::new("docker")
            .arg("run")
            .arg("-v")
            .arg(cd + ":/opt/monster")
            .arg("cksystemsteaching/selfie")
            .arg("/opt/selfie/selfie")
            .arg("-c")
            .arg("/opt/monster/symbolic/simple-if-else-symbolic-exit.c")
            .arg("-o")
            .arg("/opt/monster/symbolic/simple-if-else-symbolic-exit.riscu.o")
            .output();

        let test_file = Path::new("symbolic/simple-if-else-symbolic-exit.riscu.o");

        let ((graph, _), data_segment, elf_metadata) = build_cfg_from_file(test_file).unwrap();

        println!("{:?}", data_segment);

        let (path, branch_decisions) = create_candidate_paths(&graph)[3].clone();

        println!("{:?}", path);

        let (formula, _root) = build_dataflow_graph(
            &path,
            data_segment.as_slice(),
            &elf_metadata,
            branch_decisions,
        )
        .unwrap();

        let dot_graph = Dot::with_config(&formula, &[]);

        let mut f = File::create("tmp-graph.dot").unwrap();
        f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

        let _ = Command::new("dot")
            .arg("-Tpng")
            .arg("tmp-graph.dot")
            .arg("-o")
            .arg("main_wo_dc.png")
            .output();

        let _ = Dot::with_config(&formula, &[]);

        // TODO: test more than just this result
        // assert!(result.is_ok());

        let _ = std::fs::remove_file(test_file);
    }
}

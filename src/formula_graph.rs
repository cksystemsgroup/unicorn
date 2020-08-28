use crate::elf::ElfMetadata;
use byteorder::{ByteOrder, LittleEndian};
use core::fmt;
use petgraph::graph::NodeIndex;
use petgraph::Graph;
use riscv_decode::types::*;
use riscv_decode::Instruction;

pub type Formula = Graph<Node, ArgumentSide>;

static REG_SP: usize = 2;
static REG_A0: usize = 10;
static REG_A1: usize = 11;
static REG_A2: usize = 12;
static REG_A7: usize = 17;

#[derive(Clone, Debug, Copy, Eq, Hash, PartialEq)]
pub enum ArgumentSide {
    Lhs,
    Rhs,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct InstructionType {
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
    instruction: Instruction,
}

impl InstructionType {
    fn new(instruction: Instruction) -> Self {
        Self { instruction }
    }
}

impl fmt::Debug for InstructionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.instruction)
    }
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct ConstType {
    // can have multiple output edges, but no input edge
    value: u64,
}

impl ConstType {
    fn new(value: u64) -> Self {
        Self { value }
    }
}

impl fmt::Debug for ConstType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub struct InputType {
    // can have multiple output edges, but no input edge
    name: String,
}

impl InputType {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl fmt::Debug for InputType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub struct OutputType {
    // has 1 input edge only and 0 output edges
    name: String,
}

impl OutputType {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl fmt::Debug for OutputType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[allow(dead_code)]
pub enum Node {
    Instruction(InstructionType),
    Constant(ConstType),
    Input(InputType),
    Output(OutputType),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueType {
    Concrete(u64),
    Symbolic(NodeIndex),
    Uninitialized,
}

struct State {
    program_break: u64,
    regs: [ValueType; 32],
    memory: Vec<ValueType>,
}

impl State {
    // creates a machine state with a specifc memory size
    fn new(memory_size: usize, data_segment: &[u8], elf_metadata: ElfMetadata) -> Self {
        let mut regs = [ValueType::Concrete(0); 32];
        let mut memory = vec![ValueType::Uninitialized; memory_size / 8];

        regs[REG_SP] = ValueType::Concrete(memory_size as u64 - 8);
        regs[0] = ValueType::Concrete(0);

        let start = (elf_metadata.entry_address / 8) as usize;
        let end = start + data_segment.len() / 8;
        let range = start..end;

        println!(
            "data_segment.len(): {}   entry_address:  {}",
            data_segment.len(),
            elf_metadata.entry_address
        );

        data_segment
            .chunks(8)
            .map(LittleEndian::read_u64)
            .zip(range)
            .for_each(|(x, i)| memory[i] = ValueType::Concrete(x));

        Self {
            program_break: elf_metadata.entry_address + (data_segment.len() as u64),
            regs,
            memory,
        }
    }
}

fn create_const_node(g: &mut Formula, value: u64) -> NodeIndex {
    let constant = Node::Constant(ConstType::new(value));
    g.add_node(constant)
}

fn symbolic_op(g: &mut Formula, lhs: NodeIndex, rhs: NodeIndex, result: NodeIndex) -> ValueType {
    g.add_edge(lhs, result, ArgumentSide::Lhs);
    g.add_edge(rhs, result, ArgumentSide::Rhs);

    ValueType::Symbolic(result)
}

// fn find_node_by_alias(graph: &mut Formula, alias: u64) -> Option<NodeIndex> {
//     graph.node_indices().find(|idx| graph[*idx].alias == alias)
// }

fn execute_lui(utype: UType, state: &mut State) -> Option<NodeIndex> {
    if utype.rd() == 0 {
        return None;
    }

    let immediate = utype.imm() as u64; //sign_extend_utype(utype.imm());

    let result = ValueType::Concrete(immediate);

    println!(
        "{}  imm: {:?} -> rd: {:?}",
        instruction_to_str(Instruction::Lui(utype)),
        immediate as i64,
        result,
    );

    state.regs[utype.rd() as usize] = result;

    None
}

fn execute_itype<Op>(
    instruction: Instruction,
    itype: IType,
    graph: &mut Formula,
    state: &mut State,
    op: Op,
) -> Option<NodeIndex>
where
    Op: FnOnce(u64, u64) -> u64,
{
    if itype.rd() == 0 {
        return None;
    }

    let rs1_value = state.regs[itype.rs1() as usize];
    let immediate = sign_extend_itype_stype(itype.imm());

    let result = execute_binary_op(
        instruction,
        rs1_value,
        ValueType::Concrete(immediate),
        graph,
        op,
    );

    println!(
        "{}  rs1: {:?} imm: {:?} -> rd: {:?}",
        instruction_to_str(instruction),
        rs1_value,
        immediate as i64,
        result,
    );

    state.regs[itype.rd() as usize] = result;

    None
}

fn instruction_to_str(i: Instruction) -> &'static str {
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
        Instruction::Ecall => "ecall",
        _ => "unknown",
    }
}

fn execute_rtype<Op>(
    instruction: Instruction,
    rtype: RType,
    graph: &mut Formula,
    state: &mut State,
    op: Op,
) -> Option<NodeIndex>
where
    Op: FnOnce(u64, u64) -> u64,
{
    if rtype.rd() == 0 {
        return None;
    }

    let rs1_value = state.regs[rtype.rs1() as usize];
    let rs2_value = state.regs[rtype.rs2() as usize];

    let result = execute_binary_op(instruction, rs1_value, rs2_value, graph, op);

    println!(
        "{}  rs1: {:?} rs2: {:?} -> rd: {:?}",
        instruction_to_str(instruction),
        rs1_value,
        rs2_value,
        result,
    );

    state.regs[rtype.rd() as usize] = result;

    None
}

fn execute_binary_op<Op>(
    instruction: Instruction,
    lhs: ValueType,
    rhs: ValueType,
    graph: &mut Formula,
    op: Op,
) -> ValueType
where
    Op: FnOnce(u64, u64) -> u64,
{
    fn create_result_node(instruction: Instruction, graph: &mut Formula) -> NodeIndex {
        let node = Node::Instruction(InstructionType::new(instruction));

        graph.add_node(node)
    }

    match (lhs, rhs) {
        (ValueType::Concrete(v1), ValueType::Concrete(v2)) => ValueType::Concrete(op(v1, v2)),
        (ValueType::Symbolic(v1), ValueType::Concrete(v2)) => {
            let node = create_const_node(graph, v2);
            let res = create_result_node(instruction, graph);
            symbolic_op(graph, v1, node, res)
        }
        (ValueType::Concrete(v1), ValueType::Symbolic(v2)) => {
            let node = create_const_node(graph, v1);
            let res = create_result_node(instruction, graph);
            symbolic_op(graph, node, v2, res)
        }
        (ValueType::Symbolic(v1), ValueType::Symbolic(v2)) => {
            let res = create_result_node(instruction, graph);
            symbolic_op(graph, v1, v2, res)
        }
        _ => panic!("access to unitialized memory"),
    }
}

#[allow(dead_code)]
pub enum Syscall {
    Exit = 93,
    Read = 63,
    Write = 64,
    Openat = 56,
    Brk = 214,
}

fn eval(instruction: Instruction, graph: &mut Formula, state: &mut State) -> Option<NodeIndex> {
    match instruction {
        Instruction::Ecall => {
            match state.regs[REG_A7] {
                ValueType::Concrete(syscall_id) if syscall_id == (Syscall::Brk as u64) => {
                    if let ValueType::Concrete(new_program_break) = state.regs[REG_A0] {
                        // TODO: handle cases where program break can not be modified
                        if new_program_break < state.program_break {
                            state.regs[REG_A0] = ValueType::Concrete(state.program_break);
                        } else {
                            state.program_break = new_program_break;
                        }
                        println!("new program break: {}", new_program_break);
                    } else {
                        unimplemented!("can not handle symbolic or uninitialized program break")
                    }
                    None
                }
                ValueType::Concrete(syscall_id) if syscall_id == (Syscall::Read as u64) => {
                    // TODO: ignore FD??
                    if let ValueType::Concrete(buffer) = state.regs[REG_A1] {
                        if let ValueType::Concrete(size) = state.regs[REG_A2] {
                            // assert!(
                            //     size % 8 == 0,
                            //     "can only handle read syscalls with word width"
                            // );
                            // TODO: round up to word width.. not the best idea, right???
                            let to_add = 8 - (size % 8);
                            let words_read = (size + to_add) / 8;

                            for i in 0..words_read {
                                let name = format!("read({}, {}, {})", 0, buffer, size);
                                let node = Node::Input(InputType::new(name));
                                let node_idx = graph.add_node(node);
                                state.memory[((buffer / 8) + i) as usize] =
                                    ValueType::Symbolic(node_idx);
                            }
                        } else {
                            unimplemented!(
                                "can not handle symbolic or uinitialized size in read syscall"
                            )
                        }
                    } else {
                        unimplemented!("can not handle symbolic or uninitialized buffer address in read syscall")
                    }
                    None
                }
                ValueType::Concrete(syscall_id) if syscall_id == (Syscall::Exit as u64) => {
                    if let ValueType::Symbolic(exit_code) = state.regs[REG_A0] {
                        let root = Node::Output(OutputType::new(String::from("exit_code")));
                        let root_idx = graph.add_node(root);
                        graph.add_edge(exit_code, root_idx, ArgumentSide::Lhs);

                        Some(root_idx)
                    } else {
                        unimplemented!("exit only implemented for symbolic exit codes")
                    }
                }
                ValueType::Concrete(x) => {
                    unimplemented!("this syscall ({}) is not implemented yet", x)
                }
                ValueType::Uninitialized => unimplemented!("ecall with uninitialized syscall id"),
                ValueType::Symbolic(n) => {
                    let root = Node::Output(OutputType::new(String::from("exit_code")));
                    let root_idx = graph.add_node(root);
                    graph.add_edge(n, root_idx, ArgumentSide::Lhs);

                    Some(root_idx)
                }
            }
        }
        Instruction::Lui(utype) => execute_lui(utype, state),
        Instruction::Addi(itype) => {
            execute_itype(instruction, itype, graph, state, u64::wrapping_add)
        }
        Instruction::Add(rtype) => {
            execute_rtype(instruction, rtype, graph, state, u64::wrapping_add)
        }
        Instruction::Sub(rtype) => {
            execute_rtype(instruction, rtype, graph, state, u64::wrapping_sub)
        }
        Instruction::Mul(rtype) => {
            execute_rtype(instruction, rtype, graph, state, u64::wrapping_mul)
        }
        Instruction::Divu(rtype) => {
            execute_rtype(instruction, rtype, graph, state, u64::wrapping_div)
        }
        Instruction::Remu(rtype) => {
            execute_rtype(instruction, rtype, graph, state, u64::wrapping_rem)
        }
        Instruction::Sltu(rtype) => {
            execute_rtype(
                instruction,
                rtype,
                graph,
                state,
                |l, r| if l < r { 1 } else { 0 },
            )
        }
        Instruction::Ld(itype) => {
            if itype.rd() != 0 {
                if let ValueType::Concrete(base_address) = state.regs[itype.rs1() as usize] {
                    let immediate = sign_extend_itype_stype(itype.imm());

                    let address = base_address.wrapping_add(immediate);

                    let value = state.memory[(address / 8) as usize];

                    println!(
                        "{} rs1: {:?} imm: {} -> rd: {:?}",
                        instruction_to_str(instruction),
                        state.regs[itype.rs1() as usize],
                        immediate as i64,
                        value,
                    );

                    state.regs[itype.rd() as usize] = value;
                } else {
                    unimplemented!("can not handle symbolic addresses in LD")
                }
            }

            None
        }
        Instruction::Sd(stype) => {
            if let ValueType::Concrete(base_address) = state.regs[stype.rs1() as usize] {
                let immediate = sign_extend_itype_stype(stype.imm());

                let address = base_address.wrapping_add(immediate);

                let value = state.regs[stype.rs2() as usize];

                println!(
                    "{}  immediate: {:?} rs2: {:?} rs1: {:?} -> ",
                    instruction_to_str(instruction),
                    immediate as i64,
                    state.regs[stype.rs1() as usize],
                    value,
                );

                state.memory[(address / 8) as usize] = value;
            } else {
                unimplemented!("can not handle symbolic addresses in SD")
            }

            None
        }
        Instruction::Jal(jtype) => {
            if jtype.rd() != 0 {
                state.regs[jtype.rd() as usize] = ValueType::Concrete(0);
            }
            None
        }
        Instruction::Jalr(itype) => {
            if itype.rd() != 0 {
                state.regs[itype.rd() as usize] = ValueType::Concrete(0);
            }
            None
        }
        Instruction::Beq(_btype) => None,
        _ => unimplemented!("can not handle this instruction"),
    }
}

pub fn sign_extend(n: u64, b: u32) -> u64 {
    // assert: 0 <= n <= 2^b
    // assert: 0 < b < CPUBITWIDTH
    if n < 2_u64.pow(b - 1) {
        n
    } else {
        n.wrapping_sub(2_u64.pow(b))
    }
}

#[allow(dead_code)]
fn sign_extend_utype(imm: u32) -> u64 {
    sign_extend(imm as u64, 20)
}

fn sign_extend_itype_stype(imm: u32) -> u64 {
    sign_extend(imm as u64, 12)
}

trait ForEachUntilSome<Iter, T, R> {
    fn for_each_until_some<F>(&mut self, f: F) -> Option<R>
    where
        Iter: Iterator<Item = T>,
        F: FnMut(T) -> Option<R>;
}

impl<Iter, T, R> ForEachUntilSome<Iter, T, R> for Iter {
    fn for_each_until_some<F>(&mut self, mut f: F) -> Option<R>
    where
        Iter: Iterator<Item = T>,
        F: FnMut(T) -> Option<R>,
    {
        for element in self {
            if let Some(result) = f(element) {
                return Some(result);
            }
        }

        None
    }
}

#[allow(dead_code)]
fn build_formula_for_exit_code(
    path: &[Instruction],
    data_segment: &[u8],
    elf_metadata: ElfMetadata,
) -> Option<(Formula, NodeIndex)> {
    if let Some(Instruction::Ecall) = path.first() {
        None
    } else {
        let mut formula = Formula::new();
        let mut state = State::new(1000000, data_segment, elf_metadata);

        if let Some(root_idx) = path
            .iter()
            .for_each_until_some(|instr| eval(*instr, &mut formula, &mut state))
        {
            Some((formula, root_idx))
        } else {
            None
        }
    }
}

// TODO: need to load data segment  => then write test
#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg;
    use crate::cfg::ControlFlowGraph;
    use petgraph::dot::Dot;
    use petgraph::visit::EdgeRef;
    use serial_test::serial;
    use std::env::current_dir;
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::Path;
    use std::process::Command;

    pub fn extract_candidate_path(graph: &ControlFlowGraph) -> Vec<Instruction> {
        fn next(graph: &ControlFlowGraph, idx: NodeIndex) -> Option<NodeIndex> {
            let edges = graph.edges(idx);
            if let Some(edge) = edges.last() {
                Some(edge.target())
            } else {
                None
            }
        }
        let mut path = vec![];
        let mut idx = graph.node_indices().next().unwrap();
        path.push(idx);
        while let Some(n) = next(graph, idx) {
            path.push(n);
            idx = n;
        }
        path.iter().map(|idx| graph[*idx]).collect()
    }

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
            .arg("/opt/monster/symbolic/symbolic-exit.c")
            .arg("-o")
            .arg("/opt/monster/symbolic/symbolic-exit.riscu.o")
            .output();

        let test_file = Path::new("symbolic/symbolic-exit.riscu.o");

        let (graph, data_segment, elf_metadata) = cfg::build_from_file(test_file).unwrap();

        println!("{:?}", data_segment);

        let path = extract_candidate_path(&graph);

        println!("{:?}", path);

        let (formula, _root) =
            build_formula_for_exit_code(&path, data_segment.as_slice(), elf_metadata).unwrap();

        let dot_graph = Dot::with_config(&formula, &[]);

        let mut f = File::create("tmp-graph.dot").unwrap();
        f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

        let _ = Command::new("dot")
            .arg("-Tpng")
            .arg("tmp-graph.dot")
            .arg("-o")
            .arg("main.png")
            .output();

        // TODO: test more than just this result
        // assert!(result.is_ok());

        let _ = std::fs::remove_file(test_file);
    }
}

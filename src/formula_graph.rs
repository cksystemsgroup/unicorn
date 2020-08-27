#![allow(dead_code)]
// use crate::cfg::ControlFlowGraph;
use petgraph::graph::NodeIndex; //EdgeIndex, NodeIndex};
                                // use petgraph::visit::{GraphBase, IntoEdgeReferences, Data};
use petgraph::Graph;
// use riscv_decode::types::*;
use riscv_decode::Instruction;

pub type Formula = Graph<Node, ()>;

static REG_SP: usize = 2;
// static REG_A0: usize = 10;
static REG_A7: usize = 17;
static mut ALIAS_SEED: u64 = 1;

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct InstructionType {
    instruction: Instruction,
}

impl InstructionType {
    fn new(instruction: Instruction) -> Self {
        Self { instruction }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ConstType {
    value: u64,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct InputType {
    name: String,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct OutputType {
    name: String,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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
}

// impl petgraph::visit::IntoEdgeReferences for Node {
//     type EdgeRef = ();
//     type EdgeReferences = ();
//
//     fn edge_references(self) -> Self::EdgeReferences {
//         unimplemented!()
//     }
// }

// impl Node {
//     fn new(instruction: Instruction) -> Self {
//         Self {
//             alias: Self::fresh_alias(),
//             instruction,
//         }
//     }
//
//     fn fresh_alias() -> u64 {
//         unsafe {
//             let alias = ALIAS_SEED;
//             ALIAS_SEED += 1;
//             alias
//         }
//     }
// }

// struct State {
//     bump_pointer: u64,
//     regs: [ValueType; 32],
//     memory: Vec<ValueType>,
// }
//
// impl State {
// creates a machine state with a specifc memory size
// fn new(memory_size: usize) -> Self {
//     Self {
//         bump_pointer: 0,
//         regs: [ValueType::Concrete(0); 32],
//         memory: vec![ValueType::Concrete(0); memory_size / 8],
//     }
// }
// }

// fn build_node(
//     instruction: Instruction,
//     mem_access: Option<u64>,
//     graph: &mut Formula,
//     state: &mut State,
// ) {
//     fn find_node_by_alias(graph: &mut Formula, alias: u64) -> Option<NodeIndex> {
//         graph.node_indices().find(|idx| graph[*idx].alias == alias)
//     }
//
//     fn add_utype(instruction: Instruction, utype: UType, graph: &mut Formula, state: &mut State) {
//         let node = Node::new(instruction);
//
//         let node_index = graph.add_node(node);
//
//         let parent = state.regs[utype.rd() as usize];
//
//         if let Some(parent_node) = find_node_by_alias(graph, parent) {
//             graph.add_edge(parent_node, node_index, ());
//         }
//     }
//
//     fn add_itype(instruction: Instruction, itype: IType, graph: &mut Formula, state: &mut State) {
//         let node = Node::new(instruction);
//
//         state.regs[itype.rs1() as usize] = node.alias;
//         let node_index = graph.add_node(node);
//
//         let parent = state.regs[itype.rd() as usize];
//
//         if let Some(parent_node) = find_node_by_alias(graph, parent) {
//             graph.add_edge(parent_node, node_index, ());
//         }
//     }
//
//     fn execute_rtype<Op>(instruction: Instruction, rtype: RType, graph: &mut Formula, state: &mut State, op: Op)
//     where Op: FnOnce(u64, u64) -> u64 {
//
//         let node = Node::Instruction(InstructionType::new(instruction));
//
//         let rs1_value = state.regs[rtype.rs1() as usize];
//         let rs2_value = state.regs[rtype.rs2() as usize];
//
//         let result = match (rs1_value, rs2_value) {
//             (ValueType::Concrete(v1), ValueType::Concrete(v2)) => ValueType::Concrete(op(v1, v2)),
//             (ValueType::Symbolic(v1), ValueType::Concrete(v2)) => ValueType::Symbolic()
//         };
//
//         state.regs[rtype.rd() as usize] = result;
//
//         let node_index = graph.add_node(node);
//
//         let parent = state.regs[rtype.rd() as usize];
//
//         if let Some(parent_node) = find_node_by_alias(graph, parent) {
//             graph.add_edge(parent_node, node_index, ());
//         }
//     }
//
//     match instruction {
//         Instruction::Ecall if graph.node_count() == 0 => {
//             let root = Node::new(Instruction::Ecall);
//             state.regs[REG_A7] = root.alias;
//             graph.add_node(root);
//         }
//         Instruction::Lui(utype) => {
//             Instruction::Add(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_add(r)),
//             Instruction::Sub(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_sub(r)),
//             Instruction::Mul(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_mul(r)),
//             Instruction::Divu(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_div(r)),
//             Instruction::Remu(rtype) => exec_rtype(rtype, state, |l, r| l % r),
//             Instruction::Sltu(rtype) => exec_rtype(rtype, state, |l, r| if l < r { 1 } else { 0 }),
//             add_utype(instruction, utype, graph, state)
//         },
//         Instruction::Addi(itype) => add_itype(instruction, itype, graph, state),
//         Instruction::Add(rtype) => add_rtype(instruction, rtype, graph, state),
//         Instruction::Sub(rtype) => add_rtype(instruction, rtype, graph, state),
//         Instruction::Mul(rtype) => add_rtype(instruction, rtype, graph, state),
//         Instruction::Divu(rtype) => add_rtype(instruction, rtype, graph, state),
//         Instruction::Remu(rtype) => add_rtype(instruction, rtype, graph, state),
//         Instruction::Sltu(rtype) => add_rtype(instruction, rtype, graph, state),
//         Instruction::Ld(itype) => {
//             let parent_alias = state.regs[itype.rd() as usize];
//
//             state.memory[(mem_access.unwrap() / 8) as usize] = parent_alias;
//         }
//         Instruction::Sd(stype) => {
//             let parent_alias = state.memory[(mem_access.unwrap() / 8) as usize];
//
//             state.regs[stype.rs2() as usize] = parent_alias;
//         }
//         _ => {}
//     }
// }

// pub fn sign_extend(n: u64, b: u32) -> u64 {
//     // assert: 0 <= n <= 2^b
//     // assert: 0 < b < CPUBITWIDTH
//     if n < 2_u64.pow(b - 1) {
//         n
//     } else {
//         n.wrapping_sub(2_u64.pow(b))
//     }
// }

// fn sign_extend_utype(imm: u32) -> u64 {
//     sign_extend(imm as u64, 20)
// }
//
// fn sign_extend_itype_stype(imm: u32) -> u64 {
//     sign_extend(imm as u64, 12)
// }

// fn eval_stack_access_address(instruction: Instruction, state: &mut State) -> Option<u64> {
//     fn exec_rtype<Op: FnOnce(u64, u64) -> u64>(
//         rtype: RType,
//         state: &mut State,
//         op: Op,
//     ) -> Option<u64> {
//         if rtype.rd() != 0 {
//             state.regs[rtype.rd() as usize] = op(
//                 state.regs[rtype.rs1() as usize],
//                 state.regs[rtype.rs2() as usize],
//             );
//         }
//         None
//     }
//
//     match instruction {
//         Instruction::Lui(utype) => {
//             if utype.rd() != 0 {
//                 let imm = sign_extend_utype(utype.imm());
//                 state.regs[utype.rd() as usize] = imm << 12;
//             }
//             None
//         }
//         Instruction::Addi(itype) => {
//             if itype.rd() != 0 {
//                 state.regs[itype.rd() as usize] =
//                     state.regs[itype.rs1() as usize] + sign_extend_itype_stype(itype.imm());
//             }
//             None
//         }
//         Instruction::Add(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_add(r)),
//         Instruction::Sub(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_sub(r)),
//         Instruction::Mul(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_mul(r)),
//         Instruction::Divu(rtype) => exec_rtype(rtype, state, |l, r| l.wrapping_div(r)),
//         Instruction::Remu(rtype) => exec_rtype(rtype, state, |l, r| l % r),
//         Instruction::Sltu(rtype) => exec_rtype(rtype, state, |l, r| if l < r { 1 } else { 0 }),
//         Instruction::Ld(itype) => {
//             if itype.rd() == 0 {
//                 None
//             } else {
//                 let imm = sign_extend_itype_stype(itype.imm());
//                 let addr = state.regs[itype.rs1() as usize].wrapping_add(imm);
//                 state.regs[itype.rd() as usize] = state.memory[(addr / 8) as usize];
//                 Some(addr)
//             }
//         }
//         Instruction::Sd(stype) => {
//             let imm = sign_extend_itype_stype(stype.imm());
//             let addr = state.regs[stype.rs1() as usize].wrapping_add(imm);
//             state.memory[(addr / 8) as usize] = state.regs[stype.rs2() as usize];
//             Some(addr)
//         }
//         _ => None,
//     }
// }

// fn compute_stack_addresses(path: &[Instruction]) -> Vec<Option<u64>> {
//     let mut state = State::new(10000);
//     state.regs[REG_SP as usize] = 512;
//
//     path.iter()
//         .map(|i| eval_stack_access_address(*i, &mut state))
//         .collect()
// }

// #[allow(dead_code)]
// fn build_formula_for_exit_code(path: &[Instruction]) -> Option<Formula> {
//     if let Some(Instruction::Ecall) = path.first() {
//         None
//     } else {
//         let mut formula = Formula::new();
//         let mut state = State::new(10000);
//
//         let stack_accesses = compute_stack_addresses(path);
//
//         path.iter()
//             .zip(stack_accesses)
//             .for_each(|(instr, acc)| build_node(*instr, acc, &mut formula, &mut state));
//
//         Some(formula)
//     }
// }

#[cfg(test)]
mod tests {
    // use super::*;
    use crate::candidate_path::extract_trivial_candidate_path;
    use crate::cfg;
    // use petgraph::dot::Dot;
    use serial_test::serial;
    use std::env::current_dir;
    // use std::fs::File;
    // use std::io::prelude::*;
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
            .arg("/opt/monster/symbolic/division-by-zero-3-35.c")
            .arg("-o")
            .arg("/opt/monster/symbolic/division-by-zero-3-35.riscu.o")
            .output();

        let test_file = Path::new("symbolic/division-by-zero-3-35.riscu.o");

        let graph = cfg::build_from_file(test_file).unwrap();

        let _path = extract_trivial_candidate_path(&graph);

        // let formula = build_formula_for_exit_code(&path).unwrap();

        // let dot_graph = Dot::with_config(&formula, &[]);
        //
        // let mut f = File::create("tmp-graph.dot").unwrap();
        // f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

        // let _ = Command::new("dot")
        //     .arg("-Tpng")
        //     .arg("tmp-graph.dot")
        //     .arg("-o")
        //     .arg("main.png")
        //     .output();

        // TODO: test more than just this result
        // assert!(result.is_ok());

        let _ = std::fs::remove_file(test_file);
    }
}

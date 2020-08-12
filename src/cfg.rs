use crate::decode::{Decoder, RiscU};
use crate::elf::load_file;
use byteorder::{ByteOrder, LittleEndian};
use petgraph::graph::NodeIndex;
use petgraph::Graph;
use riscv_decode::types::*;
use riscv_decode::Instruction;
use std::path::Path;

type ControlFlowGraph = Graph<Instruction, u8>;

struct CfgBuilder {
    graph: ControlFlowGraph,
    idx: usize,
    prev_idx: usize,
    // is_finished: bool,
}

impl CfgBuilder {
    fn new() -> Self {
        CfgBuilder {
            graph: ControlFlowGraph::new(),
            idx: 0,
            prev_idx: 0,
            // is_finished: false,
        }
    }

    fn build(binary: &[u8]) -> ControlFlowGraph {
        let mut builder = CfgBuilder::new();
        let mut pipeline = Decoder::new(&mut builder);

        let words = binary
            .chunks_exact(4)
            .map(LittleEndian::read_u32)
            .collect::<Vec<u32>>();

        // while !pipeline.next.is_finished {
        while pipeline.next.idx < words.len() {
            let instruction = words[pipeline.next.idx];

            pipeline.run(instruction);
        }

        // TODO: refactor that
        // remove first edge from node 1 to node 1

        pipeline.next.graph.clone()
    }

    // TODO: only tested with Selfie RISC-U file and relies on that ELF format
    #[allow(dead_code)]
    pub fn build_from_file(file: &Path) -> Result<ControlFlowGraph, &str> {
        match unsafe { load_file(file, 1024) } {
            Some((memory_vec, meta_data)) => {
                let memory = memory_vec.as_slice();

                Ok(CfgBuilder::build(
                    memory.split_at(meta_data.code_length as usize).0,
                ))
            }
            None => todo!("error handling"),
        }
    }

    fn step(&mut self, size: usize) {
        self.prev_idx = self.idx;
        self.idx += size;
    }

    fn append_trivial(&mut self, i: Instruction) {
        let n = self.graph.add_node(i);
        self.graph.add_edge(NodeIndex::new(self.prev_idx), n, 0);
        self.step(1);
    }
}

impl RiscU for CfgBuilder {
    fn lui(&mut self, i: UType) {
        self.append_trivial(Instruction::Lui(i));
    }
    fn addi(&mut self, i: IType) {
        self.append_trivial(Instruction::Addi(i));
    }
    fn add(&mut self, i: RType) {
        self.append_trivial(Instruction::Add(i));
    }
    fn sub(&mut self, i: RType) {
        self.append_trivial(Instruction::Sub(i));
    }
    fn mul(&mut self, i: RType) {
        self.append_trivial(Instruction::Mul(i));
    }
    fn divu(&mut self, i: RType) {
        self.append_trivial(Instruction::Divu(i));
    }
    fn remu(&mut self, i: RType) {
        self.append_trivial(Instruction::Remu(i));
    }
    fn sltu(&mut self, i: RType) {
        self.append_trivial(Instruction::Sltu(i));
    }
    fn ld(&mut self, i: IType) {
        self.append_trivial(Instruction::Ld(i));
    }
    fn sd(&mut self, i: SType) {
        self.append_trivial(Instruction::Sd(i));
    }
    fn jal(&mut self, i: JType) {
        self.append_trivial(Instruction::Jal(i));
    }
    fn jalr(&mut self, i: IType) {
        self.append_trivial(Instruction::Jalr(i));
    }
    fn beq(&mut self, i: BType) {
        let n = self.graph.add_node(Instruction::Beq(i));
        self.graph.add_edge(NodeIndex::new(self.prev_idx), n, 0);

        // idx * 4 -> PC <=> PC / 4 -> idx
        if i.imm() / 4 < self.idx as u32 {
            // while loop
            self.graph
                .add_edge(n, NodeIndex::new((i.imm() / 4) as usize), 0);
            self.step(1);
        } else {
            self.step(1);
        }
    }
    fn ecall(&mut self) {
        self.append_trivial(Instruction::Ecall);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::dot::{Config, Dot};
    use serial_test::serial;
    use std::env::current_dir;
    use std::process::Command;
    use std::string::String;

    // TODO: write a unit test without dependency on selfie and external files
    #[test]
    #[serial]
    fn can_build_control_flow_graph() {
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

        let graph = CfgBuilder::build_from_file(test_file).unwrap();

        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));

        // TODO: test more than just this result
        // assert!(result.is_ok());

        let _ = std::fs::remove_file(test_file);
    }
}

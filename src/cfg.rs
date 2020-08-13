use crate::elf::load_file;
use byteorder::{ByteOrder, LittleEndian};
use petgraph::graph::NodeIndex;
use petgraph::Graph;
use riscv_decode::decode;
use riscv_decode::Instruction;
use std::path::Path;
use std::vec::Vec;

type ControlFlowGraph = Graph<Instruction, usize>;

struct CfgBuilder {
    graph: ControlFlowGraph,
    // idx: usize,
    // prev_idx: usize,
    // edges_todo: Vec::<(NodeIndex::<u32>, NodeIndex::<u32>, usize)>,
    // is_finished: bool,
}

impl CfgBuilder {
    fn new(binary: &[u8]) -> Self {
        let g = binary
            .chunks_exact(4)
            .map(LittleEndian::read_u32)
            .map(decode)
            .map(Result::unwrap)
            .fold(ControlFlowGraph::new(), |mut g, i| {
                g.add_node(i);
                g
            });

        CfgBuilder {
            graph: g,
            // idx: 0,
            // prev_idx: 0,
            // edges_todo: Vec::<(NodeIndex::<u32>, NodeIndex::<u32>, usize)>::new(),
            // is_finished: false,
        }
    }

    fn is_control_flow_instruction(&mut self, idx: NodeIndex) -> bool {
        let instruction = self.graph[idx];

        match instruction {
            Instruction::Jal(_) => true,
            Instruction::Jalr(_) => true,
            Instruction::Beq(_) => true,
            _ => false,
        }
    }

    fn compute_trivial_edges(&mut self) {
        let indices = self.graph.node_indices();
        let len = indices.len() - 1;

        let edges: Vec<(NodeIndex, NodeIndex, usize)> = indices
            .take(len)
            .filter(|i| !self.is_control_flow_instruction(*i))
            .map(|idx| {
                (
                    NodeIndex::new(idx.index()),
                    NodeIndex::new(idx.index() + 1),
                    0,
                )
            })
            .collect();

        edges.iter().for_each(|e| {
            self.graph.add_edge(e.0, e.1, e.2);
        });
    }

    fn compute_beq_edges(&mut self) {
        // let indices = self.graph.node_indices();
        // let len = indices.len() - 1;

        // let beqs = indices.filter(predicate: P)
    }

    fn build(binary: &[u8]) -> ControlFlowGraph {
        let mut builder = CfgBuilder::new(binary);

        builder.compute_trivial_edges();
        builder.compute_beq_edges();

        // TODO: refactor that
        // remove first edge from node 1 to node 1

        builder.graph
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

    // fn step(&mut self, size: usize) {
    //     self.prev_idx = self.idx;
    //     self.idx += size;
    // }

    // fn append_trivial(&mut self, i: Instruction) {
    //     let n = self.graph.add_node(i);
    //     self.step(1);
    // }
}

// impl RiscU for CfgBuilder {
//     fn lui(&mut self, i: UType) {
//         self.append_trivial(Instruction::Lui(i));
//     }
//     fn addi(&mut self, i: IType) {
//         self.append_trivial(Instruction::Addi(i));
//     }
//     fn add(&mut self, i: RType) {
//         self.append_trivial(Instruction::Add(i));
//     }
//     fn sub(&mut self, i: RType) {
//         self.append_trivial(Instruction::Sub(i));
//     }
//     fn mul(&mut self, i: RType) {
//         self.append_trivial(Instruction::Mul(i));
//     }
//     fn divu(&mut self, i: RType) {
//         self.append_trivial(Instruction::Divu(i));
//     }
//     fn remu(&mut self, i: RType) {
//         self.append_trivial(Instruction::Remu(i));
//     }
//     fn sltu(&mut self, i: RType) {
//         self.append_trivial(Instruction::Sltu(i));
//     }
//     fn ld(&mut self, i: IType) {
//         self.append_trivial(Instruction::Ld(i));
//     }
//     fn sd(&mut self, i: SType) {
//         self.append_trivial(Instruction::Sd(i));
//     }
//     fn jal(&mut self, i: JType) {
//         // JAL with ra -> function call
//         // JAL with zero -> just jump
//         let n = self.graph.add_node(Instruction::Jal(i));
//         self.graph.add_edge(NodeIndex::new(self.prev_idx), n, 0);

//         if i.rd() == 0 {
//           // jump without saving the link address
//           let destination = self.idx + i.imm() as usize / 4;
//           let e = (NodeIndex::new(n.index()), NodeIndex::new(destination), self.idx);
//           self.edges_todo.push(e);
//         } else {
//           // jump to a function

//         }
//     }
//     fn jalr(&mut self, i: IType) {
//         self.append_trivial(Instruction::Jalr(i));
//     }
//     fn beq(&mut self, i: BType) {
//         let n = self.graph.add_node(Instruction::Beq(i));
//         self.graph.add_edge(NodeIndex::new(self.prev_idx), n, 0);

//         // idx * 4 -> PC <=> PC / 4 -> idx
//         if (self.idx as u32 + i.imm()) / 4 < self.idx as u32 {
//             // while loop
//             self.graph
//                 .add_edge(n, NodeIndex::new((i.imm() / 4) as usize), 0);
//             self.step(1);
//         } else {
//             self.step(1);
//         }
//     }
//     fn ecall(&mut self) {
//         self.append_trivial(Instruction::Ecall);
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::dot::{Config, Dot};
    use serial_test::serial;
    use std::env::current_dir;
    use std::fs::File;
    use std::io::prelude::*;
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

        let dot_graph = Dot::with_config(&graph, &[Config::EdgeNoLabel]);

        let mut f = File::create("tmp-graph.dot").unwrap();
        f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

        // let _ = Command::new("dot")
        //     .arg("-Tpng")
        //     .arg("tmp-graph.dot")
        //     .arg("-o")
        //     .arg("main.png")
        //     .output();

        // println!("{:?}", ));

        // TODO: test more than just this result
        // assert!(result.is_ok());

        let _ = std::fs::remove_file(test_file);
    }
}

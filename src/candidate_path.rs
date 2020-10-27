use crate::cfg::ControlFlowGraph;
use petgraph::{
    algo::{all_simple_paths, has_path_connecting},
    graph::NodeIndex,
    Direction,
};
use riscv_decode::Instruction;

pub type CandidatePath = (Vec<Instruction>, Vec<bool>);

fn is_exit_node(g: &ControlFlowGraph, idx: NodeIndex) -> bool {
    g.neighbors_directed(idx, Direction::Outgoing).count() == 0
        && has_path_connecting(g, NodeIndex::new(0), idx, None)
}

// TODO: Remove all these temporary data structures (collect..)
pub fn create_candidate_paths(cfg: &ControlFlowGraph) -> Vec<CandidatePath> {
    cfg.node_indices()
        .filter(|i| is_exit_node(cfg, *i))
        .flat_map(|exit| {
            all_simple_paths::<Vec<NodeIndex>, &ControlFlowGraph>(
                cfg,
                NodeIndex::new(0),
                exit,
                0,
                None,
            )
        })
        .map(|path| {
            let instructions = path
                .clone()
                .into_iter()
                .map(|idx| cfg[idx])
                .collect::<Vec<Instruction>>();

            let decisions = path
                .clone()
                .into_iter()
                .enumerate()
                .filter_map(|(i, idx)| {
                    match cfg[idx] {
                        Instruction::Beq(_) => {
                            // a branch to the next idx is a decision for the false branch
                            Some(idx.index() + 1 != path[i + 1].index())
                        }
                        _ => None,
                    }
                })
                .collect::<Vec<bool>>();

            (instructions, decisions)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::*;
    use serial_test::serial;
    use std::env::current_dir;
    use std::path::Path;
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

        let ((graph, _), _, _) = build_cfg_from_file(test_file).unwrap();

        let paths = create_candidate_paths(&graph).into_iter().count();

        create_candidate_paths(&graph)
            .into_iter()
            .for_each(|(p, d)| {
                let number_of_beqs = p
                    .into_iter()
                    .filter(|i| {
                        if let Instruction::Beq(_) = i {
                            true
                        } else {
                            false
                        }
                    })
                    .count();
                let number_of_decisions = d.len();

                assert_eq!(number_of_beqs, number_of_decisions);
            });

        assert_eq!(
            paths, 28,
            "there are 28 possible candidate paths in division-by-zero-3-35"
        );
    }
}

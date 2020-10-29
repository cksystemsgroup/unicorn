use crate::{
    boolector::Boolector,
    cfg::build_cfg_from_file,
    //elf::ElfMetadata,
    exploration_strategy::ShortestPathStrategy,
    formula_graph::DataFlowGraphBuilder,
    solver::NativeSolver,
};
//use riscv_decode::Instruction;
use std::path::Path;

#[derive(Clone, Copy)]
pub enum Backend {
    Monster,
    Boolector,
}

// TODO: What should the engine return as result?
pub fn execute(input: &Path, with: Backend) -> Result<(), String> {
    let ((graph, exit_node), program) = build_cfg_from_file(input)?;

    let mut strategy = ShortestPathStrategy::new(&graph, exit_node, program.entry_address);

    match with {
        Backend::Monster => {
            let mut solver = NativeSolver::new();

            let mut executor =
                DataFlowGraphBuilder::new(1_000_000, &program, &mut strategy, &mut solver);

            executor.run();
        }
        Backend::Boolector => {
            let mut solver = Boolector::new();

            let mut executor =
                DataFlowGraphBuilder::new(1_000_000, &program, &mut strategy, &mut solver);

            executor.run();
        }
    }

    Ok(())
}

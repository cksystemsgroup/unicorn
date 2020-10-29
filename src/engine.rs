use crate::{
    bitvec::BitVector,
    boolector,
    candidate_path::create_candidate_paths,
    cfg::build_cfg_from_file,
    elf::ElfMetadata,
    formula_graph::{self, build_dataflow_graph, ExecutionResult, Formula},
    solver,
};
use riscv_decode::Instruction;
use std::{collections::HashMap, path::Path};

#[derive(Clone, Copy)]
pub enum Backend {
    Monster,
    Boolector,
}

pub fn execute(input: &Path, with: Backend) -> Result<(), String> {
    let ((graph, _), data_segment, elf_metadata) = build_cfg_from_file(input)?;

    let potential_assignment = create_candidate_paths(&graph)
        .into_iter()
        .filter_map(|path| execute_path(path, &data_segment, &elf_metadata, with))
        .next();

    if let Backend::Monster = with {
        if let Some(assignment) = potential_assignment {
            print_assignment(&assignment);
        } else {
            println!("Have not found a assignment");
        }
    }

    Ok(())
}

fn execute_path(
    path: (Vec<Instruction>, Vec<bool>),
    data_segment: &[u8],
    elf_metadata: &ElfMetadata,
    with: Backend,
) -> Option<HashMap<String, BitVector>> {
    if let Some((formula, result)) =
        build_dataflow_graph(&path.0, data_segment, &elf_metadata, path.1)
    {
        let potential_assignment = match result {
            ExecutionResult::PathUnsat => None,
            ExecutionResult::PotentialError(root) => match with {
                Backend::Monster => solver::solve(&formula, root),
                Backend::Boolector => boolector::solve(&formula, root),
            },
        };

        if let Some(assignment) = potential_assignment {
            Some(get_input_assignments(&formula, &assignment))
        } else {
            None
        }
    } else {
        None
    }
}

fn get_input_assignments(
    formula: &Formula,
    assignment: &[BitVector],
) -> HashMap<String, BitVector> {
    formula
        .node_indices()
        .filter_map(|idx| match formula[idx].clone() {
            formula_graph::Node::Input(i) => Some((i.name, assignment[idx.index()])),
            _ => None,
        })
        .collect()
}

fn print_assignment(assignment: &HashMap<String, BitVector>) {
    println!("Found an assignment:");

    assignment.iter().for_each(|(name, value)| {
        println!("{}: {:?} ({})", name, value, value.0);
    });
}

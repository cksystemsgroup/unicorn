#[macro_use]
pub mod util;

pub mod disassemble;
pub mod engine;
pub mod path_exploration;
pub mod solver;

use anyhow::Context;
pub use engine::{
    BugFinder, RaritySimulation, RaritySimulationBug, RaritySimulationError,
    RaritySimulationOptions, SymbolicExecutionBug, SymbolicExecutionEngine, SymbolicExecutionError,
    SymbolicExecutionOptions,
};
use riscu::{load_object_file, Program};
use solver::SmtType;
use std::{fs::File, io::Write, path::Path};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum MonsterError {
    #[error("I/O error")]
    IoError(anyhow::Error),

    #[error("preprocessing failed with error")]
    Preprocessing(anyhow::Error),

    #[error("symbolic execution stopped with error, {0}")]
    SymbolicExecution(SymbolicExecutionError),

    #[error("rarity simulation stopped with error")]
    RaritySimulation(RaritySimulationError),
}

pub fn load_elf<P>(input: P) -> Result<Program, MonsterError>
where
    P: AsRef<Path>,
{
    load_object_file(input).map_err(|e| {
        MonsterError::IoError(anyhow::Error::new(e).context("Failed to load object file"))
    })
}

pub fn symbolically_execute(
    program: &Program,
) -> Result<Option<SymbolicExecutionBug>, MonsterError> {
    let options = SymbolicExecutionOptions::default();
    let solver = solver::MonsterSolver::default();
    let strategy = path_exploration::ShortestPathStrategy::compute_for(program)
        .map_err(MonsterError::Preprocessing)?;

    symbolically_execute_with(program, &options, &strategy, &solver)
}

pub fn symbollically_execute_elf<P: AsRef<Path>>(
    input: P,
) -> Result<Option<SymbolicExecutionBug>, MonsterError> {
    let program = load_elf(input)?;

    symbolically_execute(&program)
}

pub fn symbolically_execute_with<Solver, Strategy>(
    program: &Program,
    options: &SymbolicExecutionOptions,
    strategy: &Strategy,
    solver: &Solver,
) -> Result<Option<SymbolicExecutionBug>, MonsterError>
where
    Strategy: path_exploration::ExplorationStrategy,
    Solver: solver::Solver,
{
    let mut engine = SymbolicExecutionEngine::new(&program, &options, strategy, solver);

    engine.run().map_err(MonsterError::SymbolicExecution)
}

pub fn symbolically_execute_elf_with<P, Solver, Strategy>(
    input: P,
    options: &SymbolicExecutionOptions,
    strategy: &Strategy,
    solver: &Solver,
) -> Result<Option<SymbolicExecutionBug>, MonsterError>
where
    P: AsRef<Path>,
    Strategy: path_exploration::ExplorationStrategy,
    Solver: solver::Solver,
{
    let program = load_elf(input)?;

    symbolically_execute_with(&program, options, strategy, solver)
}

pub fn generate_smt<Strategy, W, P>(
    input: P,
    write: W,
    options: &SymbolicExecutionOptions,
    strategy: &Strategy,
    smt_type: SmtType,
) -> Result<Option<SymbolicExecutionBug>, MonsterError>
where
    W: Write + Send + 'static,
    Strategy: path_exploration::ExplorationStrategy,
    P: AsRef<Path>,
{
    match smt_type {
        SmtType::Generic => {
            let solver = solver::SmtWriter::new::<W>(write)
                .context("failed to generate SMT file writer backend")
                .map_err(MonsterError::Preprocessing)?;

            symbolically_execute_elf_with(input, options, strategy, &solver)
        }
        #[cfg(feature = "boolector")]
        SmtType::Boolector => {
            let solver = solver::SmtWriter::new_for_solver::<solver::Boolector, W>(write)
                .context("failed to generate SMT file writer backend")
                .map_err(MonsterError::Preprocessing)?;

            symbolically_execute_elf_with(input, options, strategy, &solver)
        }
        #[cfg(feature = "z3")]
        SmtType::Z3 => {
            let solver = solver::SmtWriter::new_for_solver::<solver::Z3, W>(write)
                .context("failed to generate SMT file writer backend")
                .map_err(MonsterError::Preprocessing)?;

            symbolically_execute_elf_with(input, options, strategy, &solver)
        }
    }
}

pub fn generate_smt_to_file<Strategy, P>(
    input: P,
    output: P,
    options: &SymbolicExecutionOptions,
    strategy: &Strategy,
    smt_type: SmtType,
) -> Result<Option<SymbolicExecutionBug>, MonsterError>
where
    Strategy: path_exploration::ExplorationStrategy,
    P: AsRef<Path> + Send,
{
    let file = File::create(output)
        .context("failed to generate SMT file writer")
        .map_err(MonsterError::IoError)?;

    generate_smt(input, file, options, strategy, smt_type)
}

pub fn rarity_simulate(program: &Program) -> Result<Option<RaritySimulationBug>, MonsterError> {
    rarity_simulate_with(program, &RaritySimulationOptions::default())
}

pub fn rarity_simulate_elf<P: AsRef<Path>>(
    input: P,
) -> Result<Option<RaritySimulationBug>, MonsterError> {
    let program = load_elf(input)?;

    rarity_simulate(&program)
}

pub fn rarity_simulate_with(
    program: &Program,
    options: &RaritySimulationOptions,
) -> Result<Option<RaritySimulationBug>, MonsterError> {
    RaritySimulation::new(&options)
        .search_for_bugs(program)
        .map_err(MonsterError::RaritySimulation)
}

pub fn rarity_simulate_elf_with<P>(
    input: P,
    options: &RaritySimulationOptions,
) -> Result<Option<RaritySimulationBug>, MonsterError>
where
    P: AsRef<Path>,
{
    let program = load_elf(input)?;

    rarity_simulate_with(&program, options)
}

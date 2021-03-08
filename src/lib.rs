#[macro_use]
pub mod util;

pub mod disassemble;
pub mod engine;
pub mod path_exploration;
pub mod solver;

pub use engine::{
    BugFinder, RaritySimulation, RaritySimulationBug, RaritySimulationError,
    RaritySimulationOptions, SymbolicExecutionBug, SymbolicExecutionEngine, SymbolicExecutionError,
    SymbolicExecutionOptions,
};
use riscu::{load_object_file, Program};
use std::path::Path;
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

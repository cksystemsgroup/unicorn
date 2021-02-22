#[macro_use]
pub mod util;

pub mod disassemble;
pub mod engine;
pub mod path_exploration;
pub mod solver;

use engine::{Bug, Engine, EngineError, EngineOptions};
use riscu::{load_object_file, Program};
use std::path::Path;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum MonsterError {
    #[error("I/O error")]
    IoError(anyhow::Error),

    #[error("preprocessing failed with error")]
    Preprocessing(anyhow::Error),

    #[error("execution stopped with error")]
    Execution(EngineError),
}

pub fn load_elf<P>(input: P) -> Result<Program, MonsterError>
where
    P: AsRef<Path>,
{
    load_object_file(input).map_err(|e| {
        MonsterError::IoError(anyhow::Error::new(e).context("Failed to load object file"))
    })
}

pub fn execute(program: &Program) -> Result<Option<Bug>, MonsterError> {
    let options = EngineOptions::default();
    let solver = solver::MonsterSolver::default();
    let strategy = path_exploration::ShortestPathStrategy::compute_for(program)
        .map_err(MonsterError::Preprocessing)?;

    execute_with(program, &options, &strategy, &solver)
}

pub fn execute_elf<P: AsRef<Path>>(input: P) -> Result<Option<Bug>, MonsterError> {
    let program = load_elf(input)?;

    execute(&program)
}

pub fn execute_with<Solver, Strategy>(
    program: &Program,
    options: &EngineOptions,
    strategy: &Strategy,
    solver: &Solver,
) -> Result<Option<Bug>, MonsterError>
where
    Strategy: path_exploration::ExplorationStrategy,
    Solver: solver::Solver,
{
    let mut engine = Engine::new(&program, &options, strategy, solver);

    engine.run().map_err(MonsterError::Execution)
}

pub fn execute_elf_with<P, Solver, Strategy>(
    input: P,
    options: &EngineOptions,
    strategy: &Strategy,
    solver: &Solver,
) -> Result<Option<Bug>, MonsterError>
where
    P: AsRef<Path>,
    Strategy: path_exploration::ExplorationStrategy,
    Solver: solver::Solver,
{
    let program = load_elf(input)?;

    execute_with(&program, options, strategy, solver)
}

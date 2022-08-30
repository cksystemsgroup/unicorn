#[macro_use]
pub mod util;

pub mod disassemble;
pub mod emulate;
pub mod engine;

use riscu::{load_object_file, Program};
use std::path::Path;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum MonsterError {
    #[error("I/O error")]
    IoError(anyhow::Error),

    #[error("preprocessing failed with error")]
    Preprocessing(anyhow::Error),
}

pub fn load_elf<P>(input: P) -> Result<Program, MonsterError>
where
    P: AsRef<Path>,
{
    load_object_file(input).map_err(|e| {
        MonsterError::IoError(anyhow::Error::new(e).context("Failed to load object file"))
    })
}

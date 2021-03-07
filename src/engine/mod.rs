pub mod bug;
pub mod rarity_simulation;
pub mod symbolic_execution;
pub mod symbolic_state;
pub mod system;

pub use bug::*;
pub use rarity_simulation::*;
pub use symbolic_execution::*;

use riscu::Program;
pub trait BugFinder<Info, Error>
where
    Info: BugInfo,
    Error: std::error::Error,
{
    fn search_for_bugs(&self, program: &Program) -> Result<Option<Bug<Info>>, Error>;
}

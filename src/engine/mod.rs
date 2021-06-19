pub mod bug;
pub mod memory;
pub mod profiler;
pub mod rarity_simulation;
pub mod symbolic_execution;
pub mod symbolic_state;
pub mod system;

pub use bug::*;
pub use memory::*;
pub use profiler::*;
pub use rarity_simulation::*;
pub use symbolic_execution::*;

use riscu::Program;
pub trait BugFinder<Info, Error>
where
    Info: BugInfo,
    Error: std::error::Error,
{
    fn search_for_bugs(&mut self, program: &Program) -> Result<Option<Bug<Info>>, Error>;
}

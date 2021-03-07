use log::trace;
use monster::{self, engine::rarity_simulation::*, rarity_simulate_elf_with};
use rayon::prelude::*;
use utils::{compile_riscu, init, with_temp_dir};

#[test]
fn test_rarity_simulation() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, Some(&["three-level-nested-loop-1-35.c"])).for_each(
            |(source, object)| {
                let result = rarity_simulate_elf_with(
                    &object,
                    &RaritySimulationOptions {
                        amount_of_states: 1,
                        selection: 1,
                        iterations: 1,
                        ..Default::default()
                    },
                );

                trace!("execution finished: {:?}", result);

                assert!(
                    matches!(result, Ok(None)),
                    "can rarity simulate '{}' without error ({:?})",
                    source.to_str().unwrap(),
                    result,
                );
            },
        );
    });
}

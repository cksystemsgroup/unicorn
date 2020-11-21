mod common;

use common::{compile_riscu, init};
use monster::engine;
use rayon::prelude::*;

const TEST_FILES: [&str; 6] = [
    "arithmetic.c",
    "if-else.c",
    "invalid-memory-access-2-35.c",
    "division-by-zero-3-35.c",
    "simple-assignment-1-35.c",
    "test-sltu.c",
];

fn execute_riscu(names: &'static [&str], solver: engine::Backend) {
    init();
    compile_riscu(Some(names)).1.for_each(|(source, object)| {
        let result = engine::execute(object, solver, 100000);

        assert!(
            result.is_ok(),
            format!(
                "can symbolically execute '{}' without error",
                source.to_str().unwrap()
            )
        );
    });
}

#[test]
fn execute_riscu_with_monster_solver() {
    execute_riscu(&TEST_FILES, engine::Backend::Monster);
}

#[test]
fn execute_riscu_with_boolector_solver() {
    execute_riscu(&TEST_FILES, engine::Backend::Boolector);
}

#[test]
fn execute_riscu_with_z3_solver() {
    execute_riscu(&TEST_FILES, engine::Backend::Z3);
}

#[test]
fn execute_engine_for_endless_loops() {
    init();

    compile_riscu(Some(&["endless-loop.c"]))
        .1
        .for_each(|(_, object)| {
            engine::execute(object, engine::Backend::Monster, 5).unwrap();
        });
}

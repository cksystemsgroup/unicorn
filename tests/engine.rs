mod common;

use common::{compile_all_riscu, init};
use monster::engine;
use rayon::prelude::*;

const TEST_FILES: [&str; 3] = ["/arithmetic.c", "/if-else.c", "/test-sltu.c"];

fn execute_riscu(names: &[&str], solver: engine::Backend) {
    init();
    compile_all_riscu()
        .1
        .filter(|(source, _)| names.iter().any(|name| source.ends_with(name)))
        .for_each(|(source, object)| {
            let result = engine::execute(object, solver);

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

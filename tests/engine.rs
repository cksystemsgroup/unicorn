mod common;

use bytesize::ByteSize;
use common::{compile_riscu, init};
use monster::{self, engine::*};
use rayon::prelude::*;

// TODO: Test if the execution engine delivers the right assignments,
// instead of just testing if it crashes.
const TEST_FILES: [&str; 16] = [
    "arithmetic.c",
    "if-else.c",
    "invalid-memory-access-2-35.c",
    "division-by-zero-3-35.c",
    "simple-assignment-1-35.c",
    "test-sltu.c",
    "memory-access-1-35.",
    "nested-if-else-reverse-1-35",
    "nested-recursion-1-35.",
    "recursive-ackermann-1-35.c",
    "recursive-factorial-1-35.c",
    "recursive-fibonacci-1-10.c",
    "simple-if-else-1-35.c",
    "simple-increasing-loop-1-35.c",
    "two-level-nested-loop-1-35.c",
    "three-level-nested-loop-1-35",
];

fn execute_riscu(names: &'static [&str], solver: Backend) {
    init();
    compile_riscu(Some(names)).1.for_each(|(source, object)| {
        let result = execute(object, solver, 100000, ByteSize::mb(1));

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
    execute_riscu(&TEST_FILES, Backend::Monster);
}

#[test]
fn execute_riscu_with_boolector_solver() {
    execute_riscu(&TEST_FILES, Backend::Boolector);
}

#[test]
fn execute_riscu_with_z3_solver() {
    execute_riscu(&TEST_FILES, Backend::Z3);
}

#[test]
fn execute_with_different_memory_sizes() {
    init();

    compile_riscu(Some(&["/recursive-ackermann-1-35.c"]))
        .1
        .for_each(|(source, object)| {
            [1, 64, 512, 1024].iter().for_each(move |size| {
                let result = execute(&object, Backend::Monster, 100, ByteSize::mb(*size));

                assert!(
                    result.is_ok(),
                    format!(
                        "can symbolically execute '{}' without error",
                        source.to_str().unwrap()
                    )
                );
            });
        });
}

#[test]
fn execute_engine_for_endless_loops() {
    init();

    compile_riscu(Some(&["endless-loop.c"]))
        .1
        .for_each(|(_, object)| {
            execute(object, Backend::Monster, 5, ByteSize::mb(1)).unwrap();
        });
}

mod common;

use bytesize::ByteSize;
use common::{compile_riscu, init, with_temp_dir};
use log::trace;
use monster::{self, bug::Bug, engine::*};
use rayon::prelude::*;
use std::path::PathBuf;

const TEST_FILES: [&str; 14] = [
    "arithmetic.c",
    "if-else.c", // needs timeout
    "invalid-memory-access-2-35.c",
    "division-by-zero-3-35.c",
    "simple-assignment-1-35.c",
    "test-sltu.c",
    //"memory-access-1-35.c",
    "nested-if-else-reverse-1-35",
    "nested-recursion-1-35.c",
    "recursive-ackermann-1-35.c",
    "recursive-factorial-1-35.c",
    "recursive-fibonacci-1-10.c",
    "simple-if-else-1-35.c",
    "simple-increasing-loop-1-35.c",
    "two-level-nested-loop-1-35.c",
    //"three-level-nested-loop-1-35",
];

// TODO: Fix this test case
#[test]
fn execute_riscu_with_monster_solver() {
    execute_riscu_examples(&TEST_FILES, Backend::Monster);
}

#[test]
#[cfg(feature = "boolector-solver")]
fn execute_riscu_with_boolector_solver() {
    execute_riscu_examples(&TEST_FILES, Backend::Boolector);
}

#[test]
#[cfg(feature = "z3-solver")]
fn execute_riscu_with_z3_solver() {
    execute_riscu_examples(&TEST_FILES, Backend::Z3);
}

#[test]
fn execute_with_different_memory_sizes() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, Some(&["recursive-fibonacci-1-35.c"])).for_each(|(source, object)| {
            [1, 64, 512, 1024].iter().for_each(move |size| {
                let result = execute(&object, Backend::Monster, 200, ByteSize::mb(*size));

                assert!(
                    result.is_ok(),
                    format!(
                        "can symbolically execute '{}' without error",
                        source.to_str().unwrap()
                    )
                );
            });
        });
    });
}

#[test]
fn execute_engine_for_endless_loops() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, Some(&["endless-loop.c"])).for_each(|(_, object)| {
            assert!(
                execute(object, Backend::Monster, 5, ByteSize::mb(1)).is_err(),
                "has to error with depth error"
            );
        });
    });
}

fn execute_riscu_examples(names: &'static [&str], solver: Backend) {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, Some(names))
            .for_each(|(source, object)| execute_riscu(source, object, solver));
    });
}

fn execute_riscu(source: PathBuf, object: PathBuf, solver: Backend) {
    let file_name = source.file_name().unwrap().to_str().unwrap();

    let depth = match file_name {
        "two-level-nested-loop-1-35.c" => 200,
        "recursive-fibonacci-1-10.c" => 300,
        _ => 1000,
    };

    let result = execute(object, solver, depth, ByteSize::mb(1));

    trace!("execution finished: {:?}", result);

    assert!(
        result.is_ok(),
        format!(
            "can symbolically execute '{}' without error",
            source.to_str().unwrap()
        )
    );

    let possible_bug = result.unwrap();

    assert!(
        possible_bug.is_some(),
        format!("found a bug in '{}'", source.to_str().unwrap())
    );

    let bug = possible_bug.unwrap();

    assert!(
        matches!(
            (file_name, bug.clone()),
            ("arithmetic.c", Bug::ExitCodeGreaterZero { .. }) |
                ("invalid-memory-access-2-35.c", Bug::AccessToOutOfRangeAddress { .. }) |
                ("if-else.c", Bug::ExitCodeGreaterZero { .. }) |
                ("division-by-zero-3-35.c", Bug::DivisionByZero { .. }) |
                ("simple-assignment-1-35.c", Bug::ExitCodeGreaterZero { .. }) |
                ("test-sltu.c", Bug::ExitCodeGreaterZero { .. }) |
                //("memory-access-1-35.c", Bug::
                ("nested-if-else-reverse-1-35", Bug::ExitCodeGreaterZero { .. }) |
                ("nested-recursion-1-35.c", Bug::ExitCodeGreaterZero { .. }) |
                ("recursive-ackermann-1-35.c", Bug::ExitCodeGreaterZero { .. }) |
                ("recursive-factorial-1-35.c", Bug::ExitCodeGreaterZero { .. }) |
                ("recursive-fibonacci-1-10.c", Bug::ExitCodeGreaterZero { .. }) |
                ("simple-if-else-1-35.c", Bug::ExitCodeGreaterZero { .. }) |
                ("simple-increasing-loop-1-35.c", Bug::ExitCodeGreaterZero { .. }) |
                ("two-level-nested-loop-1-35.c", Bug::ExitCodeGreaterZero { .. })
        ),
        "found right bug type (actual: {}) for {}",
        bug,
        file_name
    );
}

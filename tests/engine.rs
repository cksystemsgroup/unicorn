mod common;

use bytesize::ByteSize;
use common::{compile_riscu, init};
use log::trace;
use monster::{self, bug::Bug, engine::*};
use rayon::prelude::*;

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

fn execute_riscu(names: &'static [&str], solver: Backend) {
    init();
    compile_riscu(Some(names)).1.for_each(|(source, object)| {
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
            match (file_name, bug.clone()) {
                ("arithmetic.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("invalid-memory-access-2-35.c", Bug::AccessToOutOfRangeAddress { .. }) => true,
                ("if-else.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("division-by-zero-3-35.c", Bug::DivisionByZero { .. }) => true,
                ("simple-assignment-1-35.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("test-sltu.c", Bug::ExitCodeGreaterZero { .. }) => true,
                //("memory-access-1-35.c", Bug::
                ("nested-if-else-reverse-1-35", Bug::ExitCodeGreaterZero { .. }) => true,
                ("nested-recursion-1-35.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("recursive-ackermann-1-35.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("recursive-factorial-1-35.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("recursive-fibonacci-1-10.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("simple-if-else-1-35.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("simple-increasing-loop-1-35.c", Bug::ExitCodeGreaterZero { .. }) => true,
                ("two-level-nested-loop-1-35.c", Bug::ExitCodeGreaterZero { .. }) => true,
                _ => false,
            },
            "found right bug type (actual: {}) for {}",
            bug,
            file_name
        );
    });
}

// TODO: Fix this test case
//#[test]
//fn execute_riscu_with_monster_solver() {
//execute_riscu(&TEST_FILES, Backend::Monster);
//}

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

    compile_riscu(Some(&["recursive-fibonacci-1-35.c"]))
        .1
        .for_each(|(source, object)| {
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
}

#[test]
fn execute_engine_for_endless_loops() {
    init();

    compile_riscu(Some(&["endless-loop.c"]))
        .1
        .for_each(|(_, object)| {
            assert!(
                execute(object, Backend::Monster, 5, ByteSize::mb(1)).is_err(),
                "has to error with depth error"
            );
        });
}

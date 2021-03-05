use bytesize::ByteSize;
use log::trace;
use monster::{
    self,
    engine::{Bug, EngineOptions},
    execute_with, load_elf,
    path_exploration::ShortestPathStrategy,
    solver::{MonsterSolver, Solver},
    MonsterError,
};
use rayon::prelude::*;
use std::{
    path::{Path, PathBuf},
    time::Duration,
};
use utils::{compile_riscu, init, with_temp_dir};

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

#[test]
fn execute_riscu_with_monster_solver() {
    // need a big timeout because of the slow Github runners
    let solver = MonsterSolver::new(Duration::new(5, 0));
    execute_riscu_examples(&TEST_FILES, &solver);
}

#[test]
#[cfg(feature = "boolector-solver")]
fn execute_riscu_with_boolector_solver() {
    use monster::solver::Boolector;

    let solver = Boolector::default();

    execute_riscu_examples(&TEST_FILES, &solver);
}

#[test]
#[cfg(feature = "z3-solver")]
fn execute_riscu_with_z3_solver() {
    use monster::solver::Z3;

    let solver = Z3::default();

    execute_riscu_examples(&TEST_FILES, &solver);
}

#[test]
fn execute_with_different_memory_sizes() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, Some(&["recursive-fibonacci-1-35.c"])).for_each(|(source, object)| {
            [1, 64, 512, 1024].iter().for_each(move |size| {
                let options = EngineOptions {
                    max_exection_depth: 200,
                    memory_size: ByteSize::mb(*size),
                };

                let result = execute_default_with(&object, &options);

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
            let options = EngineOptions {
                max_exection_depth: 5,
                ..Default::default()
            };

            assert!(
                execute_default_with(object, &options).is_err(),
                "has to error with depth error"
            );
        });
    });
}

fn execute_default_with<P: AsRef<Path>>(
    object: P,
    options: &EngineOptions,
) -> Result<Option<Bug>, MonsterError> {
    // need a big timeout because of the slow Github runners
    let solver = MonsterSolver::new(Duration::new(5, 0));

    execute_default_with_solver(object, options, &solver)
}

fn execute_default_with_solver<P: AsRef<Path>, S: Solver>(
    object: P,
    options: &EngineOptions,
    solver: &S,
) -> Result<Option<Bug>, MonsterError> {
    let program = load_elf(object).unwrap();
    let strategy = ShortestPathStrategy::compute_for(&program).unwrap();

    execute_with(&program, options, &strategy, solver)
}

fn execute_riscu_examples<S: Solver>(names: &'static [&str], solver: &S) {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, Some(names))
            .for_each(|(source, object)| execute_riscu(source, object, solver));
    });
}

fn execute_riscu<S: Solver>(source: PathBuf, object: PathBuf, solver: &S) {
    let file_name = source.file_name().unwrap().to_str().unwrap();

    let options = EngineOptions {
        max_exection_depth: match file_name {
            "two-level-nested-loop-1-35.c" => 200,
            "recursive-fibonacci-1-10.c" => 300,
            _ => 1000,
        },
        ..Default::default()
    };

    let result = execute_default_with_solver(object, &options, solver);

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

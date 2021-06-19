use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use lazy_static::lazy_static;
use monster::{
    load_elf,
    path_exploration::{CoinFlipStrategy, ShortestPathStrategy},
    symbolically_execute_with, SymbolicExecutionOptions,
};
use std::time::Duration;
use utils::TestFileCompiler;

#[cfg(feature = "z3")]
use monster::solver::Z3;

const TEST_FILES: [&str; 23] = [
    "count_up_down-1.c",
    "simple_3-1.c",
    "sum01-1.c",
    "demonstration.c",
    "arithmetic.c",
    "echo-line.c",
    "if-else.c",
    "invalid-memory-access-2-35.c",
    "division-by-zero-3-35.c",
    "simple-assignment-1-35.c",
    "test-sltu.c",
    "memory-invalid-read.c",
    "memory-invalid-write.c",
    "memory-uninitialized-write.c",
    "nested-if-else-reverse-1-35",
    "nested-recursion-1-35.c",
    "recursive-ackermann-1-35.c",
    "recursive-factorial-1-35.c",
    "recursive-fibonacci-1-10.c",
    "simple-if-else-1-35.c",
    "simple-increasing-loop-1-35.c",
    "two-level-nested-loop-1-35.c",
    "multiple-read.c",
];

lazy_static! {
    static ref COMPILER: TestFileCompiler = TestFileCompiler::new(&TEST_FILES);
}

#[cfg(feature = "z3")]
criterion_group!(benches, bench_shortes_paths_vs_coin_flip);
criterion_main!(benches);

#[cfg(feature = "z3")]
fn bench_shortes_paths_vs_coin_flip(c: &mut Criterion) {
    let mut group = c.benchmark_group("Path Exploration Strategies");

    group.sample_size(10).warm_up_time(Duration::from_secs(1));

    COMPILER
        .objects()
        .iter()
        .zip(COMPILER.sources())
        .for_each(|(object, source)| {
            let program = load_elf(object).unwrap();

            let options = SymbolicExecutionOptions {
                max_exection_depth: match source.file_name().unwrap().to_str().unwrap() {
                    "two-level-nested-loop-1-35.c" => 230,
                    "recursive-fibonacci-1-10.c" => 300,
                    "count_up_down-1.c" => 1000000,
                    _ => 1000,
                },
                ..Default::default()
            };

            group.bench_with_input(
                BenchmarkId::new(
                    "Shortest Path",
                    source.file_name().unwrap().to_str().unwrap(),
                ),
                &(&program, &options),
                |b, (program, options)| {
                    let strategy = ShortestPathStrategy::compute_for(program)
                        .expect("computable for test file");

                    b.iter(|| {
                        symbolically_execute_with(program, options, &strategy, &Z3::default())
                            .expect("successfull result")
                            .0
                            .expect("bug found");
                    })
                },
            );
        });

    COMPILER
        .objects()
        .iter()
        .zip(COMPILER.sources())
        .for_each(|(object, source)| {
            let program = load_elf(object).unwrap();

            let options = SymbolicExecutionOptions {
                max_exection_depth: match source.file_name().unwrap().to_str().unwrap() {
                    "two-level-nested-loop-1-35.c" => 230,
                    "recursive-fibonacci-1-10.c" => 300,
                    "count_up_down-1.c" => 1000000,
                    _ => 1000,
                },
                ..Default::default()
            };

            group.bench_with_input(
                BenchmarkId::new("Coin Flip", source.file_name().unwrap().to_str().unwrap()),
                &(&program, &options),
                |b, (program, options)| {
                    let strategy = CoinFlipStrategy::new();

                    b.iter(|| {
                        symbolically_execute_with(program, options, &strategy, &Z3::default())
                            .expect("successfull result")
                            .0
                            .expect("bug found");
                    })
                },
            );
        });

    group.finish();
}

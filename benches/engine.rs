use bytesize::ByteSize;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use lazy_static::lazy_static;
use monster::{
    engine::rarity_simulation::*,
    engine::SymbolicExecutionOptions,
    load_elf,
    path_exploration::ShortestPathStrategy,
    rarity_simulate_elf_with,
    solver::{MonsterSolver, Solver},
    symbolically_execute_with,
};
use std::{
    path::{Path, PathBuf},
    time::Duration,
};
use utils::TestFileCompiler;

#[cfg(feature = "boolector")]
use monster::solver::Boolector;

#[cfg(feature = "z3")]
use monster::solver::Z3;

const TEST_FILES: [&str; 4] = [
    "demonstration.c",
    "if-simple.c",
    "long-loop-fixed.c",
    "select-rare.c",
];

const SAMPLE_SIZE: usize = 100;
const WARM_UP_TIME: Duration = Duration::from_secs(1);

lazy_static! {
    static ref COMPILER: TestFileCompiler = TestFileCompiler::new(&TEST_FILES);
}

criterion_group!(benches, bench_solver_individual);
criterion_main!(benches);

#[allow(dead_code)] // disabled, kept for demonstration
fn bench_demonstration(c: &mut Criterion) {
    let object_file = COMPILER.object("demonstration.c");

    let mut group = c.benchmark_group("EngineDemo");

    group.sample_size(1000).warm_up_time(Duration::from_secs(3));

    group.bench_function("Monster", |b| {
        b.iter(|| execute_symbolically::<MonsterSolver, &PathBuf>(object_file))
    });
    #[cfg(feature = "boolector")]
    group.bench_function("Boolector", |b| {
        b.iter(|| execute_symbolically::<Boolector, &PathBuf>(object_file))
    });
    #[cfg(feature = "z3")]
    group.bench_function("Z3", |b| {
        b.iter(|| execute_symbolically::<Z3, &PathBuf>(object_file))
    });

    group.finish();
}

#[allow(dead_code)] // disabled, kept for demonstration
fn bench_solver_avg(c: &mut Criterion) {
    let mut group = c.benchmark_group("EngineAvg");

    group.sample_size(SAMPLE_SIZE).warm_up_time(WARM_UP_TIME);

    group.bench_function("Monster", |b| {
        b.iter(|| execute_symbolically_all::<MonsterSolver>(COMPILER.objects()))
    });
    #[cfg(feature = "boolector")]
    group.bench_function("Boolector", |b| {
        b.iter(|| execute_symbolically_all::<Boolector>(COMPILER.objects()))
    });
    #[cfg(feature = "z3")]
    group.bench_function("Z3", |b| {
        b.iter(|| execute_symbolically_all::<Z3>(COMPILER.objects()))
    });

    group.finish();
}

fn bench_solver_individual(c: &mut Criterion) {
    let mut group = c.benchmark_group("Engine");

    group.sample_size(SAMPLE_SIZE).warm_up_time(WARM_UP_TIME);

    COMPILER.objects().iter().for_each(|source| {
        let id = BenchmarkId::new("Monster", source.file_name().unwrap().to_str().unwrap());
        group.bench_function(id, |b| {
            b.iter(|| execute_symbolically::<MonsterSolver, &PathBuf>(source))
        });
    });

    #[cfg(feature = "boolector")]
    COMPILER.objects().iter().for_each(|source| {
        let id = BenchmarkId::new("Boolector", source.file_name().unwrap().to_str().unwrap());
        group.bench_function(id, |b| {
            b.iter(|| execute_symbolically::<Boolector, &PathBuf>(source))
        });
    });

    #[cfg(feature = "z3")]
    COMPILER.objects().iter().for_each(|source| {
        let id = BenchmarkId::new("Z3", source.file_name().unwrap().to_str().unwrap());
        group.bench_function(id, |b| {
            b.iter(|| execute_symbolically::<Z3, &PathBuf>(source))
        });
    });

    COMPILER.objects().iter().for_each(|object| {
        let id = BenchmarkId::new("Rarity", object.file_name().unwrap().to_str().unwrap());
        group.bench_function(id, |b| b.iter(|| execute_rarity::<&PathBuf>(object)));
    });

    group.finish();
}

fn execute_symbolically_all<S: Solver>(objects: &[PathBuf]) {
    objects.iter().for_each(|object_path| {
        execute_symbolically::<S, &PathBuf>(object_path);
    })
}

fn execute_symbolically<S: Solver, P: AsRef<Path>>(object_path: P) {
    let program = load_elf(object_path).unwrap();
    let options = SymbolicExecutionOptions {
        max_exection_depth: 5000000,
        memory_size: ByteSize(400000),
        ..Default::default()
    };
    let solver = S::default();
    let strategy = ShortestPathStrategy::compute_for(&program).unwrap();
    let _result = symbolically_execute_with(&program, &options, &strategy, &solver);
}

fn execute_rarity<P: AsRef<Path>>(object_path: P) {
    let options = RaritySimulationOptions {
        amount_of_states: 10,
        iterations: 2,
        ..Default::default()
    };
    let _result = rarity_simulate_elf_with(&object_path, &options);
}

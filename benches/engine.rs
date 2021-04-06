use bytesize::ByteSize;
use criterion::{criterion_group, criterion_main, Criterion};
use lazy_static::lazy_static;
use monster::{
    engine::SymbolicExecutionOptions,
    load_elf,
    path_exploration::ShortestPathStrategy,
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

    let mut group = c.benchmark_group("Engine");

    group.sample_size(1000).warm_up_time(Duration::from_secs(3));

    group.bench_function("Monster", |b| {
        b.iter(|| execute_single::<MonsterSolver, &PathBuf>(object_file))
    });
    #[cfg(feature = "boolector")]
    group.bench_function("Boolector", |b| {
        b.iter(|| execute_single::<Boolector, &PathBuf>(object_file))
    });
    #[cfg(feature = "z3")]
    group.bench_function("Z3", |b| {
        b.iter(|| execute_single::<Z3, &PathBuf>(object_file))
    });
}

#[allow(dead_code)] // disabled, kept for demonstration
fn bench_solver_avg(c: &mut Criterion) {
    let mut group = c.benchmark_group("Engine");

    group.sample_size(SAMPLE_SIZE).warm_up_time(WARM_UP_TIME);

    group.bench_function("Monster", |b| {
        b.iter(|| execute_all::<MonsterSolver>(COMPILER.objects()))
    });
    #[cfg(feature = "boolector")]
    group.bench_function("Boolector", |b| {
        b.iter(|| execute_all::<Boolector>(COMPILER.objects()))
    });
    #[cfg(feature = "z3")]
    group.bench_function("Z3", |b| b.iter(|| execute_all::<Z3>(COMPILER.objects())));
}

fn bench_solver_individual(c: &mut Criterion) {
    {
        let mut monster_grp = c.benchmark_group("Monster");
        monster_grp
            .sample_size(SAMPLE_SIZE)
            .warm_up_time(WARM_UP_TIME);

        COMPILER.objects().iter().for_each(|source| {
            let id = source.file_name().unwrap().to_str().unwrap();
            monster_grp.bench_function(id, |b| {
                b.iter(|| execute_single::<MonsterSolver, &PathBuf>(source))
            });
        });
    }

    #[cfg(feature = "boolector")]
    {
        let mut boolector_grp = c.benchmark_group("Boolector");
        boolector_grp
            .sample_size(SAMPLE_SIZE)
            .warm_up_time(WARM_UP_TIME);

        COMPILER.objects().iter().for_each(|source| {
            let id = source.file_name().unwrap().to_str().unwrap();
            boolector_grp.bench_function(id, |b| {
                b.iter(|| execute_single::<Boolector, &PathBuf>(source))
            });
        });
    }

    #[cfg(feature = "z3")]
    {
        let mut z3_grp = c.benchmark_group("Z3");
        z3_grp.sample_size(SAMPLE_SIZE).warm_up_time(WARM_UP_TIME);

        COMPILER.objects().iter().for_each(|source| {
            let id = source.file_name().unwrap().to_str().unwrap();
            z3_grp.bench_function(id, |b| b.iter(|| execute_single::<Z3, &PathBuf>(source)));
        });
    }
}

fn execute_all<S: Solver>(objects: &[PathBuf]) {
    objects.iter().for_each(|object_path| {
        let _result = execute_single::<S, &PathBuf>(object_path);
    })
}

fn execute_single<S: Solver, P: AsRef<Path>>(object_path: P) {
    let program = load_elf(object_path).unwrap();
    let options = SymbolicExecutionOptions {
        max_exection_depth: 5000000,
        memory_size: ByteSize(400000),
    };
    let solver = S::default();
    let strategy = ShortestPathStrategy::compute_for(&program).unwrap();

    let _result = symbolically_execute_with(&program, &options, &strategy, &solver);
}

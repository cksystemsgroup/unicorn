use bytesize::ByteSize;
use criterion::{criterion_group, criterion_main, Criterion};
use monster::{
    engine::EngineOptions,
    execute_with, load_elf,
    path_exploration::ShortestPathStrategy,
    solver::{MonsterSolver, Solver},
};
use rayon::prelude::*;
use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
    sync::{Arc, Once},
    time::Duration,
};
use tempfile::{tempdir, TempDir};
use utils::compile_riscu;

#[cfg(feature = "boolector-solver")]
use monster::solver::Boolector;

#[cfg(feature = "z3-solver")]
use monster::solver::Z3;

const TEST_FILES: [&str; 4] = [
    "count_up_down-1.c",
    "simple_3-1.c",
    "sum01-1.c",
    "demonstration.c",
];
static mut TEST_OBJECT_FILES: Option<Vec<PathBuf>> = None;
static mut TEMP_DIR: Option<Arc<TempDir>> = None;
static COMPILE_TEST_FILES: Once = Once::new();

criterion_group!(
    benches,
    bench_demonstration,
    bench_solver_avg,
    bench_solver_individual
);
criterion_main!(benches);

fn bench_demonstration(c: &mut Criterion) {
    let object_file = compile_test_file("demonstration.c");

    let mut group = c.benchmark_group("Engine");

    group.sample_size(1000).warm_up_time(Duration::from_secs(3));

    group.bench_function("Monster", |b| {
        b.iter(|| execute_single::<MonsterSolver, &PathBuf>(&object_file))
    });
    #[cfg(feature = "boolector-solver")]
    group.bench_function("Boolector", |b| {
        b.iter(|| execute_single::<Boolector, &PathBuf>(&object_file))
    });
    #[cfg(feature = "z3-solver")]
    group.bench_function("Z3", |b| {
        b.iter(|| execute_single::<Z3, &PathBuf>(&object_file))
    });
}

fn bench_solver_avg(c: &mut Criterion) {
    let mut group = c.benchmark_group("Engine");
    let object_files = compile_test_files();

    group.sample_size(100).warm_up_time(Duration::from_secs(1));

    group.bench_function("Monster", |b| {
        b.iter(|| execute_all::<MonsterSolver>(&object_files))
    });
    #[cfg(feature = "boolector-solver")]
    group.bench_function("Boolector", |b| {
        b.iter(|| execute_all::<Boolector>(&object_files))
    });
    #[cfg(feature = "z3-solver")]
    group.bench_function("Z3", |b| b.iter(|| execute_all::<Z3>(&object_files)));
}

fn bench_solver_individual(c: &mut Criterion) {
    let object_files = compile_test_files();

    {
        let mut monster_grp = c.benchmark_group("Monster");
        monster_grp
            .warm_up_time(Duration::from_secs(2))
            .sample_size(30);

        object_files.iter().for_each(|source| {
            let id = source.file_name().unwrap().to_str().unwrap();
            monster_grp.bench_function(id, |b| {
                b.iter(|| execute_single::<MonsterSolver, &PathBuf>(source))
            });
        });
    }

    #[cfg(feature = "boolector-solver")]
    {
        let mut boolector_grp = c.benchmark_group("Boolector");
        boolector_grp
            .warm_up_time(Duration::from_secs(2))
            .sample_size(30);
        object_files.iter().for_each(|source| {
            let id = source.file_name().unwrap().to_str().unwrap();
            boolector_grp.bench_function(id, |b| {
                b.iter(|| execute_single::<Boolector, &PathBuf>(source))
            });
        });
    }

    #[cfg(feature = "z3-solver")]
    {
        let mut z3_grp = c.benchmark_group("Z3");
        z3_grp.warm_up_time(Duration::from_secs(2)).sample_size(30);
        object_files.iter().for_each(|source| {
            let id = source.file_name().unwrap().to_str().unwrap();
            z3_grp.bench_function(id, |b| b.iter(|| execute_single::<Z3, &PathBuf>(source)));
        });
    }
}

fn compile_test_files() -> Vec<PathBuf> {
    unsafe {
        COMPILE_TEST_FILES.call_once(|| {
            let tmp_dir = Arc::new(tempdir().unwrap());
            TEMP_DIR = Some(tmp_dir.clone());

            TEST_OBJECT_FILES = Some(
                compile_riscu(tmp_dir.clone(), Some(&TEST_FILES))
                    .map(|(_source, object)| object)
                    .collect(),
            );
        });

        TEST_OBJECT_FILES.clone().unwrap()
    }
}

fn compile_test_file(file_name: &str) -> PathBuf {
    let object_files = compile_test_files();

    let mut file_name = PathBuf::from(file_name);
    file_name.set_extension("o");
    let file_name = file_name.to_str().unwrap();

    object_files
        .iter()
        .find(|p| p.file_name() == Some(OsStr::new(file_name)))
        .unwrap()
        .clone()
}

fn execute_all<S: Solver>(objects: &[PathBuf]) {
    objects.iter().for_each(|object_path| {
        let _result = execute_single::<S, &PathBuf>(object_path);
    })
}

fn execute_single<S: Solver, P: AsRef<Path>>(object_path: P) {
    let program = load_elf(object_path).unwrap();
    let options = EngineOptions {
        max_exection_depth: 5000000,
        memory_size: ByteSize(400000),
    };
    let solver = S::default();
    let strategy = ShortestPathStrategy::compute_for(&program).unwrap();

    let _result = execute_with(&program, &options, &strategy, &solver);
}

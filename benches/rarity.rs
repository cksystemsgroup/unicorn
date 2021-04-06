use criterion::{criterion_group, criterion_main, Criterion};
use lazy_static::lazy_static;
use monster::{self, engine::rarity_simulation::*, rarity_simulate_elf_with};
use std::{
    path::{Path, PathBuf},
    time::Duration,
};
use utils::TestFileCompiler;

const TEST_FILES: [&str; 4] = [
    "demonstration.c",
    "if-simple.c",
    "long-loop-fixed.c",
    "select-rare.c",
];

const SAMPLE_SIZE: usize = 50;
const WARM_UP_TIME: Duration = Duration::from_secs(1);

lazy_static! {
    static ref COMPILER: TestFileCompiler = TestFileCompiler::new(&TEST_FILES);
}

criterion_group!(benches, bench_rarity);
criterion_main!(benches);

fn bench_rarity(c: &mut Criterion) {
    let mut group = c.benchmark_group("Rarity");

    group.sample_size(SAMPLE_SIZE).warm_up_time(WARM_UP_TIME);

    COMPILER.objects().iter().for_each(|object| {
        let id = object.file_name().unwrap().to_str().unwrap();
        group.bench_function(id, |b| b.iter(|| execute_single::<&PathBuf>(object)));
    });

    group.finish();
}

fn execute_single<P: AsRef<Path>>(object_path: P) {
    let options = RaritySimulationOptions {
        amount_of_states: 10,
        iterations: 2,
        ..Default::default()
    };
    let _result = rarity_simulate_elf_with(&object_path, &options);
}

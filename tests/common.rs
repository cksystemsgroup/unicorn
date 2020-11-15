use log::info;
use rayon::{iter::ParallelBridge, prelude::*};
use std::{
    fs::{canonicalize, read_dir},
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
    time::Instant,
};
use tempfile::{tempdir, TempDir};

pub fn init() {
    let _ = env_logger::builder().is_test(true).try_init();
}

pub fn compile<P>(source_file: P, destination_file: P) -> Result<PathBuf, &'static str>
where
    P: AsRef<Path>,
{
    let src = canonicalize(source_file).unwrap();

    let src_directory = src.parent().unwrap();
    let src_file_name = src.file_name().unwrap();

    let dst_directory = destination_file.as_ref().parent().unwrap();
    let dst_file_name = destination_file.as_ref().file_name().unwrap();

    Command::new("docker")
        .arg("run")
        .arg("-v")
        .arg(format!(
            "{}:/opt/monster_src",
            src_directory.to_str().unwrap()
        ))
        .arg("-v")
        .arg(format!(
            "{}:/opt/monster_dst",
            dst_directory.to_str().unwrap()
        ))
        .arg("cksystemsteaching/selfie")
        .arg("/opt/selfie/selfie")
        .arg("-c")
        .arg(format!(
            "/opt/monster_src/{}",
            src_file_name.to_str().unwrap()
        ))
        .arg("-o")
        .arg(format!(
            "/opt/monster_dst/{}",
            dst_file_name.to_str().unwrap()
        ))
        .output()
        .map_err(|_| "Selfie C* compile command was not successfull")?;

    Ok(destination_file.as_ref().to_path_buf())
}

/// Convert a dot file into a png file (depends on graphviz)
#[allow(dead_code)]
pub fn convert_dot_to_png_and_check<P>(source: P) -> Result<(), &'static str>
where
    P: AsRef<Path>,
{
    let output = source.as_ref().with_extension("png");

    time("dot-to-png", || {
        Command::new("dot")
            .arg("-Tpng")
            .arg(source.as_ref().to_path_buf())
            .arg("-o")
            .arg(output.to_path_buf())
            .output()
            .map_err(|_| "Cannot convert CFG to png file (is graphviz installed?)")
    })?;

    assert!(
        output.exists(),
        "PNG could be created for {:?}",
        source.as_ref()
    );

    Ok(())
}

pub fn time<F, R>(s: &str, mut f: F) -> R
where
    F: FnMut() -> R,
{
    let start = Instant::now();
    let result = f();
    let end = Instant::now();

    info!("{}: {:?}", s, end.duration_since(start));

    result
}

pub fn compile_all_riscu() -> (
    Arc<TempDir>,
    impl ParallelIterator<Item = (PathBuf, PathBuf)>,
) {
    let tmp_dir = Arc::new(tempdir().unwrap());
    let tmp_dir_clone = tmp_dir.clone();

    let iter = read_dir("examples")
        .unwrap()
        .par_bridge()
        .map(|dir_entry| dir_entry.unwrap().path())
        .filter(|path| {
            if let Some(extension) = path.extension() {
                extension == "c"
            } else {
                false
            }
        })
        .map(move |source_file| {
            let dst_file_path = tmp_dir
                .path()
                .join(source_file.with_extension("o").file_name().unwrap());

            let result_path = time(
                format!("compile: {}", source_file.to_str().unwrap()).as_str(),
                || compile(source_file.clone(), dst_file_path.clone()).unwrap(),
            );

            (source_file, result_path)
        });

    (tmp_dir_clone, iter)
}

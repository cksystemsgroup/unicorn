use log::info;
use rayon::{iter::ParallelBridge, prelude::*};
use std::{
    env,
    fs::{canonicalize, read_dir},
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Once},
    time::Instant,
};
use tempfile::{tempdir, TempDir};
use which::which;

static INIT_LOGGER: Once = Once::new();
static INIT_SELFIE: Once = Once::new();
static mut SELFIE_PATH: Option<PathBuf> = None;

pub fn init() {
    INIT_LOGGER.call_once(|| {
        let _ = env_logger::builder().is_test(true).try_init();
    });
}

pub fn compile<P>(
    selfie_path: P,
    source_file: P,
    destination_file: P,
) -> Result<PathBuf, &'static str>
where
    P: AsRef<Path>,
{
    let src = canonicalize(source_file.as_ref()).unwrap();

    Command::new(selfie_path.as_ref())
        .arg("-c")
        .arg(src)
        .arg("-o")
        .arg(destination_file.as_ref())
        .output()
        .expect("Selfie C* compile command was not successfull");

    Ok(destination_file.as_ref().to_path_buf())
}

fn ensure_selfie_build_tools_installed() {
    let _ =
        which("make").expect("Can not find make in $PATH. Make has to be installed on your system");

    if cfg!(target_os = "windows") {
        let _ = which("gcc")
            .expect("Can not find gcc in $env:PATH. Mingw64 has to be installed on your system");
    } else {
        let _ = which("cc")
            .expect("Can not find cc in $PATH. A C compiler has to be installed on your system");
    }
}

fn ensure_selfie_installed() -> PathBuf {
    ensure_selfie_build_tools_installed();

    unsafe {
        INIT_SELFIE.call_once(|| {
            let repo_dir = env::temp_dir().join("monster-crate-selfie-installation");

            if !repo_dir.exists() {
                std::fs::create_dir(&repo_dir).unwrap();

                Command::new("git")
                    .arg("clone")
                    .arg("https://github.com/christianmoesl/selfie")
                    .arg(&repo_dir)
                    .output()
                    .expect("Selfie Git repository could not be cloned from Github");
            }

            Command::new("git")
                .arg("pull")
                .arg("--rebase")
                .current_dir(&repo_dir)
                .output()
                .expect("Selfie Git repository could not be updated");

            let mut cmd = Command::new("make");

            if cfg!(target_os = "windows") {
                cmd.env("CC", "gcc");
            }

            cmd.arg("selfie")
                .current_dir(&repo_dir)
                .output()
                .expect("Selfie can not be compiled");

            SELFIE_PATH = Some(repo_dir.join(if cfg!(target_os = "windows") {
                "selfie.exe"
            } else {
                "selfie"
            }));
        });

        SELFIE_PATH
            .clone()
            .expect("path should be initialized here")
    }
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

pub fn with_temp_dir<F, R>(f: F) -> R
where
    F: FnOnce(Arc<TempDir>) -> R,
{
    let temp_dir = Arc::new(tempdir().unwrap());

    f(temp_dir)
}

pub fn compile_riscu(
    tmp_dir: Arc<TempDir>,
    filter: Option<&'static [&str]>,
) -> impl ParallelIterator<Item = (PathBuf, PathBuf)> {
    let selfie_path = ensure_selfie_installed();

    read_dir("examples")
        .unwrap()
        .par_bridge()
        .map(|dir_entry| dir_entry.unwrap().path())
        .filter(move |path| {
            if let Some(extension) = path.extension() {
                if let Some(names) = filter {
                    names.iter().any(|name| path.ends_with(name))
                } else {
                    extension == "c"
                }
            } else {
                false
            }
        })
        .map(move |source_file| {
            let dst_file_path = tmp_dir
                .path()
                .join(source_file.with_extension("o").file_name().unwrap());

            let result_path = time(
                format!("compile: {}", source_file.display()).as_str(),
                || compile(&selfie_path, &source_file, &dst_file_path).unwrap(),
            );

            (source_file, result_path)
        })
}

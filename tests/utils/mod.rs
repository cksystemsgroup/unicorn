use log::{debug, info};
use rayon::{iter::ParallelBridge, prelude::*};
use std::{
    env,
    ffi::OsStr,
    fs::read_dir,
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
    let selfie_output = Command::new(selfie_path.as_ref())
        .arg("-c")
        .arg(source_file.as_ref())
        .arg("-o")
        .arg(destination_file.as_ref())
        .output()
        .expect("Selfie C* compile command was not successfull");

    assert!(
        selfie_output.status.success(),
        "Selfie C* compile command for {} returned status code: {}",
        source_file.as_ref().display(),
        selfie_output.status
    );

    debug!(
        "selfie output:\n{}",
        String::from_utf8(selfie_output.stdout).unwrap()
    );

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
                    .arg("https://github.com/cksystemsteaching/selfie")
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

    let examples_path = env::current_dir().unwrap().join("examples");

    read_dir(examples_path)
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
                || {
                    let result = compile(&selfie_path, &source_file, &dst_file_path);

                    assert!(
                        result.is_ok(),
                        "selfie can compile {}",
                        source_file.display()
                    );

                    result.unwrap()
                },
            );

            (source_file, result_path)
        })
}

#[allow(dead_code)]
pub struct TestFileCompiler {
    source_files: Vec<PathBuf>,
    object_files: Vec<PathBuf>,
    _temp_dir: Arc<TempDir>,
}

#[allow(dead_code)]
impl TestFileCompiler {
    pub fn new(source_files: &'static [&'static str]) -> Self {
        let temp_dir = Arc::new(tempdir().unwrap());

        let results: Vec<_> = compile_riscu(temp_dir.clone(), Some(source_files)).collect();

        let source_files: Vec<_> = results.iter().map(|(s, _)| s).cloned().collect();
        let object_files: Vec<_> = results.iter().map(|(_, o)| o).cloned().collect();

        Self {
            source_files,
            object_files,
            _temp_dir: temp_dir,
        }
    }

    pub fn objects(&self) -> &[PathBuf] {
        &self.object_files
    }

    pub fn sources(&self) -> &[PathBuf] {
        &self.source_files
    }

    pub fn object(&self, source_file_name: &'static str) -> &PathBuf {
        let mut file_name = PathBuf::from(source_file_name);
        file_name.set_extension("o");
        let file_name = file_name.to_str().unwrap();

        self.object_files
            .iter()
            .find(|p| p.file_name() == Some(OsStr::new(file_name)))
            .unwrap()
    }

    pub fn source(&self, source_file_name: &'static str) -> &PathBuf {
        self.source_files
            .iter()
            .find(|p| p.file_name() == Some(OsStr::new(source_file_name)))
            .unwrap()
    }
}

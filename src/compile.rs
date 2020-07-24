use std::str;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const RUST_TARGET_DIR: &str = "symbolic/target/riscv64gc-unknown-linux-gnu/debug";

pub fn compile_example(source_file: &Path) -> Result<PathBuf, &str> {
    match source_file.extension() {
        Some(extension) if extension == "c" => compile_c(source_file),
        Some(extension) if extension == "rs" => compile_rust(source_file),
        _ => Err("file is not a C or Rust source file"),
    }
}

fn validate_example(source_file: &Path) -> Result<(), &str> {
    let path = Path::new(source_file);

    let canonical_dir = path.canonicalize()
        .map_err(|_| "is not a valid file path")?;

    let parent_dir = canonical_dir.parent()
        .ok_or_else(|| "choose a source file from ./symbolic")?;

    let symbolic_dir = Path::new("symbolic").canonicalize().unwrap();

    if parent_dir != symbolic_dir {
        Err("source file has to be in ./symbolic")
    } else if !path.exists() {
        Err("example has to exist on file system")
    } else {
        Ok(())
    }
}

fn compile_c(source_file: &Path) -> Result<PathBuf, &str> {
    validate_example(source_file)?;

    let directory = source_file.parent().unwrap();
    let target = source_file.with_extension("o");

    Command::new("make")
        .arg(target.file_name().unwrap())
        .current_dir(directory)
        .output()
        .map_err(|_| "Rust compile command was not successfull")?;

    Ok(target)
}

fn compile_rust(source_file: &Path) -> Result<PathBuf, &str> {
    validate_example(source_file)?;

    let directory = source_file.parent().unwrap();
    let target = source_file.with_extension("");

    Command::new("cross")
        .arg("build")
        .arg("--target")
        .arg("riscv64gc-unknown-linux-gnu")
        .arg("--bin")
        .arg(target.file_name().unwrap())
        .current_dir(directory)
        .output()
        .map_err(|_| "Rust compile command was not successfull")?;

    let out = Path::new(RUST_TARGET_DIR).join(target.file_name().unwrap());

    fs::copy(&out, &target).map_err(|_| "unable to copy compilation result to destination")?;

    Ok(target)
}

fn clean(object_file: &Path) {
    let _ = fs::remove_file(object_file);

    let rust_object = format!("{}/{}", RUST_TARGET_DIR, object_file.file_stem().unwrap().to_str().unwrap());

    let _ = fs::remove_file(rust_object);
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    #[test]
    #[serial] // execute it in serial because we manipulate files
    fn compile_c_source_file() {
        let source_path = Path::new("symbolic/division-by-zero-3-35.c");
        let result = compile_example(source_path);

        assert!(result.is_ok(), "can compile C source file");

        let path_buf = result.unwrap();

        assert!(path_buf.exists(), "compiled object file exists");

        clean(path_buf.as_path());
    }

    #[test]
    #[serial] // execute it in serial because we manipulate files
    fn compile_rust_source_file() {
        let source_path = Path::new("symbolic/division-by-zero-3-35.rs");

        let result = compile_example(source_path);

        let status = Command::new("docker")
            .arg("info")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .status();

        assert!(status.is_ok() && status.unwrap().success(), "docker daemon is running");

        assert!(result.is_ok(), "can compile Rust source file");

        let path_buf = result.unwrap();

        assert!(path_buf.exists(), "compiled object file exists");

        clean(path_buf.as_path());
    }
}

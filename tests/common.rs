use std::{
    env::current_dir,
    path::{Path, PathBuf},
    process::Command,
};

pub fn compile(source_file: &Path) -> Result<PathBuf, &str> {
    let directory = source_file.parent().unwrap();
    let target = source_file.with_extension("o");

    Command::new("docker")
        .arg("run")
        .arg("-v")
        .arg(format!(
            "{}:/opt/monster",
            current_dir().unwrap().to_str().unwrap()
        ))
        .arg("cksystemsteaching/selfie")
        .arg("/opt/selfie/selfie")
        .arg("-c")
        .arg(format!("/opt/monster/{}", source_file.to_str().unwrap()))
        .arg("-o")
        .arg(format!("/opt/monster/{}", target.to_str().unwrap()))
        .current_dir(directory)
        .output()
        .map_err(|_| "Selfie C* compile command was not successfull")?;

    Ok(target)
}

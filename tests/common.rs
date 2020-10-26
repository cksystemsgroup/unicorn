#![allow(dead_code)]

use std::{
    env::current_dir,
    fs::read_dir,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

pub fn compile<P>(source_file: P) -> Result<PathBuf, &'static str>
where
    P: AsRef<Path>,
{
    let directory = source_file.as_ref().parent().unwrap();
    let target = source_file.as_ref().with_extension("o");

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
        .arg(format!(
            "/opt/monster/{}",
            source_file.as_ref().to_str().unwrap()
        ))
        .arg("-o")
        .arg(format!("/opt/monster/{}", target.to_str().unwrap()))
        .current_dir(directory)
        .output()
        .map_err(|_| "Selfie C* compile command was not successfull")?;

    Ok(target)
}

/// Convert a dot file into a png file (depends on graphviz)
pub fn convert_dot_to_png<P>(source: P, output: P) -> Result<(), &'static str>
where
    P: AsRef<Path>,
{
    Command::new("dot")
        .arg("-Tpng")
        .arg(source.as_ref().to_path_buf())
        .arg("-o")
        .arg(output.as_ref().to_path_buf())
        .output()
        .map_err(|_| "Cannot convert CFG to png file (is graphviz installed?)")?;

    Ok(())
}

pub fn time<F, R>(s: String, mut f: F) -> R
where
    F: FnMut() -> R,
{
    let start = Instant::now();
    let result = f();
    let end = Instant::now();

    println!("{}: {:?}", s, end.duration_since(start));

    result
}

pub fn forall_compiled_riscu<F>(f: F)
where
    F: Fn(PathBuf) + Send + Sync + 'static,
{
    let compiled = read_dir("symbolic")
        .unwrap()
        .map(|dir_entry| dir_entry.unwrap().path())
        .filter(|path| {
            if let Some(extension) = path.extension() {
                extension == "c"
            } else {
                false
            }
        })
        .map(|input_source| {
            time(
                format!("compile: {}", input_source.to_str().unwrap()),
                || compile(input_source.clone()).unwrap(),
            )
        });

    //let f = std::sync::Arc::new(f);

    compiled.for_each(|binary_file_name| {
        //let f = f.clone();
        //thread::spawn(move || {
        time(
            format!("compute CFG: {}", binary_file_name.to_str().unwrap()),
            || {
                f(binary_file_name.clone());
            },
        );
        //})
    });
    //.for_each(|t| {
    //t.join().unwrap();
    //})
}

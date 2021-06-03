use lazy_static::lazy_static;
use log::info;
use monster::{
    self, load_elf, path_exploration::ShortestPathStrategy, solver::ExternalSolver,
    symbolically_execute_elf_with, SymbolicExecutionOptions,
};
use std::{ffi::CString, fs, path::PathBuf, sync::Arc};
use tempfile::TempDir;
use utils::{init, with_temp_dir, TestFileCompiler};

const TEST_FILES: [&str; 19] = [
    "echo-line.c",
    "division-by-zero-3-35.c",
    "simple-assignment-1-35.c",
    "if-else.c", // needs timeout
    "arithmetic.c",
    "test-remu.c",
    "test-sltu.c",
    "test-sltu-2.c",
    "simple-if-else-1-35.c",
    "invalid-memory-access-2-35.c",
    //
    // TODO: Fix uncoditional exits in combination with external solver first:
    // "memory-invalid-read.c",
    // "memory-invalid-write.c",
    // "memory-access-1-35.c",
    //
    "memory-uninitialized-write.c",
    "nested-if-else-reverse-1-35",
    "nested-recursion-1-35.c",
    "recursive-ackermann-1-35.c",
    "recursive-factorial-1-35.c",
    "recursive-fibonacci-1-10.c",
    "simple-increasing-loop-1-35.c",
    "two-level-nested-loop-1-35.c",
    //"three-level-nested-loop-1-35",
    "multiple-read.c",
];

lazy_static! {
    static ref COMPILER: TestFileCompiler = TestFileCompiler::new(&TEST_FILES);
}

#[test]
fn generate_smt_files() {
    init();

    with_temp_dir(|dir| {
        COMPILER
            .sources()
            .iter()
            .cloned()
            .zip(COMPILER.objects().iter().cloned())
            .map(|files| generate_smt(dir.clone(), "", files))
            .for_each(|_| {});
    });
}

#[test]
#[cfg(feature = "z3-sys")]
fn solve_generated_smt_files_with_z3() {
    init();

    with_temp_dir(|dir| {
        COMPILER
            .sources()
            .iter()
            .cloned()
            .zip(COMPILER.objects().iter().cloned())
            .map(|files| {
                generate_smt(
                    dir.clone(),
                    "(set-option :model_validate true)\n(set-option :model true)\n",
                    files,
                )
            })
            .for_each(solve_with_z3);
    });
}

#[cfg(feature = "z3-sys")]
fn solve_with_z3(files: (PathBuf, PathBuf, PathBuf)) {
    use z3_sys::{
        Z3_del_config, Z3_del_context, Z3_mk_config, Z3_mk_context, Z3_mk_solver,
        Z3_set_param_value, Z3_solver_check, Z3_solver_dec_ref, Z3_solver_from_file,
        Z3_solver_get_model, Z3_solver_inc_ref, Z3_L_TRUE,
    };

    unsafe {
        let config = Z3_mk_config();

        let param_key = CString::new("model").unwrap();
        let param_value = CString::new("true").unwrap();
        Z3_set_param_value(config, param_key.as_ptr(), param_value.as_ptr());

        let context = Z3_mk_context(config);

        let solver = Z3_mk_solver(context);
        Z3_solver_inc_ref(context, solver);

        let file_path = CString::new(files.2.as_os_str().to_str().unwrap()).unwrap();

        log::debug!("parse SMT-lib 2 file: {}", file_path.to_str().unwrap());

        let contents = std::fs::read_to_string(file_path.to_str().unwrap())
            .expect("Something went wrong reading the file");

        log::debug!("with contents:\n{}", contents);

        Z3_solver_from_file(context, solver, file_path.as_ptr());

        let result = Z3_solver_check(context, solver);

        assert!(
            result == Z3_L_TRUE,
            "Z3 is able to solve generated SMT-lib files"
        );

        let model = Z3_solver_get_model(context, solver);

        assert!(!model.is_null(), "returns a valid model");

        Z3_solver_dec_ref(context, solver);
        Z3_del_context(context);
        Z3_del_config(config);
    }
}

#[test]
#[cfg(feature = "boolector-sys")]
fn solve_generated_smt_files_with_boolector() {
    init();

    with_temp_dir(|dir| {
        COMPILER
            .sources()
            .iter()
            .cloned()
            .zip(COMPILER.objects().iter().cloned())
            .map(|files| {
                generate_smt(
                    dir.clone(),
                    "(set-option :incremental true)\n(set-option :produce-models true)\n",
                    files,
                )
            })
            .for_each(solve_with_boolector);
    });
}

#[cfg(feature = "boolector-sys")]
fn solve_with_boolector(files: (PathBuf, PathBuf, PathBuf)) {
    use boolector_sys::{boolector_new, boolector_parse_smt2};

    unsafe {
        let btor = boolector_new();

        let file_path = CString::new(files.2.as_os_str().to_str().unwrap()).unwrap();

        let in_filemode = CString::new("r").unwrap();
        let infile = libc::fopen(file_path.as_ptr(), in_filemode.as_ptr());
        let infile_name = CString::new("input").unwrap();

        let out_filename = CString::new("./tmp.txt").unwrap();
        let out_filemode = CString::new("w").unwrap();
        let outfile = libc::fopen(out_filename.as_ptr(), out_filemode.as_ptr());

        let error_msg = libc::malloc(16) as *mut *mut i8;
        let status = libc::malloc(8) as *mut i32;

        let result = boolector_parse_smt2(
            btor,
            infile,
            infile_name.as_ptr(),
            outfile,
            error_msg,
            status,
        );

        assert!(
            result == boolector_sys::BtorSolverResult_BTOR_RESULT_SAT as i32,
            "boolector solved SMT-lib file {} without error (result code: {})",
            files.2.display(),
            result
        );

        libc::fclose(infile);
    }
}

fn prepend_smt(smt_file: PathBuf, smt: &str) {
    let contents = fs::read_to_string(smt_file.as_os_str()).expect("smt file is readable");

    let mut new_contents = smt.to_owned();

    new_contents.push_str(&contents);

    fs::write(smt_file, new_contents).expect("smt file is writable");
}

fn generate_smt(
    dir: Arc<TempDir>,
    smt_options: &str,
    files: (PathBuf, PathBuf),
) -> (PathBuf, PathBuf, PathBuf) {
    info!("generate SMT-lib file for: {}", files.1.display());

    let output_path = dir.as_ref().path().join(
        files
            .1
            .with_extension("smt")
            .file_name()
            .map(PathBuf::from)
            .unwrap(),
    );

    let solver = ExternalSolver::new(&output_path).unwrap();

    let program = load_elf(&files.1).unwrap();
    let strategy = ShortestPathStrategy::compute_for(&program).unwrap();

    let result = symbolically_execute_elf_with(
        &files.1,
        &SymbolicExecutionOptions::default(),
        &strategy,
        &solver,
    );

    assert!(
        result.is_ok(),
        "can generate SMT-lib file for '{}' without error",
        files.0.to_str().unwrap()
    );

    prepend_smt(output_path.clone(), smt_options);

    (files.0, files.1, output_path)
}

use std::fmt::Display;
use std::path::Path;

mod bitvec;
mod candidate_path;
mod cfg;
mod cli;
mod compile;
mod dead_code_elimination;
mod decode;
mod disassemble;
mod elf;
mod engine;
mod formula_graph;
mod iterator;
mod ternary;

use compile::compile_example;
use disassemble::disassemble_riscu;

fn main() {
    let matches = cli::args().get_matches();

    fn handle_error<R, E, F>(f: F) -> R
    where
        E: Display,
        F: FnOnce() -> Result<R, E>,
    {
        match f() {
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1);
            }
            Ok(x) => x,
        }
    }

    match matches.subcommand() {
        ("disassemble", Some(disassemble_args)) => handle_error(|| {
            let input = Path::new(disassemble_args.value_of("input-file").unwrap());
            disassemble_riscu(Path::new(input))
        }),
        ("compile", Some(compiler_args)) => handle_error(|| -> Result<(), String> {
            let compiler = compiler_args.value_of("compiler").unwrap();

            let input = Path::new(compiler_args.value_of("input-file").unwrap());

            compile_example(input, Some(compiler))?;

            Ok(())
        }),
        ("cfg", Some(cfg_args)) => {
            handle_error(|| -> Result<(), String> {
                let input = Path::new(cfg_args.value_of("input-file").unwrap());
                let output = Path::new(cfg_args.value_of("output-file").unwrap());

                let (graph, _, _) = cfg::build_from_file(Path::new(input))?;

                if let Some(_format @ "png") = cfg_args.value_of("format") {
                    let tmp = Path::new(".tmp-cfg.dot");

                    cfg::write_to_file(&graph, tmp).map_err(|e| e.to_string())?;

                    cfg::convert_dot_to_png(tmp, output)?;

                    std::fs::remove_file(tmp).map_err(|e| e.to_string())?;
                } else {
                    cfg::write_to_file(&graph, output).map_err(|e| e.to_string())?;
                }

                Ok(())
            });
        }
        _ => unreachable!(),
    }
}

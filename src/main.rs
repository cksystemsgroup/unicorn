use clap::{App, Arg};
use std::fmt::Display;
use std::path::Path;

mod bitvec;
mod candidate_path;
mod cfg;
mod compile;
mod decode;
mod disassemble;
mod elf;
mod engine;
mod formula_graph;
mod ternary;

use compile::compile_example;
use disassemble::disassemble_riscu;

fn main() {
    let args = App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS").replace(":", ", ").as_str())
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .arg(
            Arg::with_name("compile")
                .short('c')
                .long("compile")
                .value_name("FILE")
                .about("compile a source file")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("disassemble")
                .short('d')
                .long("disassemble")
                .value_name("FILE")
                .about("disassemble a RISC-U ELF binary")
                .takes_value(true),
        )
        .subcommand(
            App::new("cfg")
                .about("control flow graph generation from RISC-U ELF binary")
                .arg(
                    Arg::with_name("input-file")
                        .about("RISC-U binary to be used as input")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::with_name("output-file")
                        .about("the output")
                        .short('o')
                        .long("output-file")
                        .takes_value(true)
                        .value_name("FILE")
                        .default_value("cfg.dot"),
                )
                .arg(
                    Arg::with_name("format")
                        .about("the file format of the generated CFG")
                        .short('f')
                        .long("format")
                        .takes_value(true)
                        .possible_values(&["dot", "png"])
                        .default_value("dot"),
                ),
        )
        .get_matches();

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

    if let Some(source) = args.value_of("compile") {
        handle_error(|| compile_example(Path::new(source)));
    } else if let Some(object) = args.value_of("disassemble") {
        handle_error(|| disassemble_riscu(Path::new(object)));
    }

    if let Some(ref args) = args.subcommand_matches("cfg") {
        handle_error(|| -> Result<(), String> {
            let input = Path::new(args.value_of("input-file").unwrap());
            let output = Path::new(args.value_of("output-file").unwrap());

            let graph = cfg::build_from_file(Path::new(input))?;

            if let Some(_format @ "png") = args.value_of("format") {
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
}

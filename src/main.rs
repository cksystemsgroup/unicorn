use clap::{App, Arg};
use std::path::Path;
use std::process;
use std::fmt::Display;

mod elf;
mod decode;
mod compile;
mod disassemble;

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
                .takes_value(true)
                .required(true),
        )
        .arg(
            Arg::with_name("disassemble")
                .short('d')
                .long("disassemble")
                .value_name("FILE")
                .about("disassemble a RISC-U ELF binary")
                .takes_value(true)
                .required(true),
        )
        .get_matches();

    fn handle_error<R, E: Display>(result: Result<R, E>) -> R {
        match result {
            Err(e) => {
                println!("{}", e);
                std::process::exit(1);
            }
            Ok(x) => x
        }
    }

    if let Some(source) = args.value_of("compile") {
        handle_error(compile_example(Path::new(source)));
    } else if let Some(object) = args.value_of("disassemble") {
        handle_error(disassemble_riscu(Path::new(object)));
    }
}

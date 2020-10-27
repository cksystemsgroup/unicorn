use std::fmt::Display;
use std::path::Path;

mod cli;

use monster::{
    cfg::{build_cfg_from_file, write_to_file},
    disassemble::disassemble_riscu,
    engine,
};

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
        Some(("disassemble", disassemble_args)) => handle_error(|| {
            let input = Path::new(disassemble_args.value_of("input-file").unwrap());
            disassemble_riscu(Path::new(input))
        }),
        Some(("cfg", cfg_args)) => {
            handle_error(|| -> Result<(), String> {
                let input = Path::new(cfg_args.value_of("input-file").unwrap());
                let output = Path::new(cfg_args.value_of("output-file").unwrap());

                let ((graph, _), _, _) = build_cfg_from_file(Path::new(input))?;

                write_to_file(&graph, output).map_err(|e| e.to_string())?;

                Ok(())
            });
        }
        Some(("execute", args)) => {
            handle_error(|| -> Result<(), String> {
                let input = Path::new(args.value_of("input-file").unwrap());
                let solver = args.value_of("solver").unwrap();

                match solver {
                    "monster" => engine::execute(input, engine::Backend::Monster),
                    "boolector" => engine::execute(input, engine::Backend::Boolector),
                    _ => unreachable!(),
                }
            });
        }
        _ => unreachable!(),
    }
}

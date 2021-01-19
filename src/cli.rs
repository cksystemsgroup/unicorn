use crate::engine::{DEFAULT_MAX_EXECUTION_DEPTH, DEFAULT_MEMORY_SIZE};
use anyhow::Result;
use clap::{crate_authors, crate_description, crate_version, App, AppSettings, Arg, ArgMatches};
use const_format::formatcp;

pub const LOGGING_LEVELS: [&str; 5] = ["trace", "debug", "info", "warn", "error"];
pub const SOLVER: [&str; 4] = ["monster", "boolector", "z3", "external"];

pub fn expect_arg<'a>(m: &'a ArgMatches, arg: &str) -> &'a str {
    m.value_of(arg)
        .unwrap_or_else(|| panic!("argument \"{}\" has to be set in CLI at all times", arg))
}

fn is_u64(v: &str) -> Result<(), String> {
    v.parse::<u64>().map(|_| ()).map_err(|e| e.to_string())
}

fn is_valid_memory_size(v: &str) -> Result<(), String> {
    is_u64(v).and_then(|_| {
        let memory_size = v.parse::<u64>().expect("have checked that already");

        let valid_range = 1_u64..=1024_u64;

        if valid_range.contains(&memory_size) {
            Ok(())
        } else {
            Err(String::from("memory size has to be in range: 1 - 1024"))
        }
    })
}

fn is_ratio(v: &str) -> Result<(), String> {
    let valid_range = 0.0_f64..=1.0f64;

    match v.parse::<f64>() {
        Ok(ratio) => {
            if valid_range.contains(&ratio) {
                Ok(())
            } else {
                Err("Expected range between 0.0 and 1.0".to_string())
            }
        }
        Err(err) => Err(err.to_string()),
    }
}

pub fn args() -> App<'static> {
    App::new("Monster")
        .version(crate_version!())
        .author(crate_authors!(", "))
        .about(crate_description!())
        .arg(
            Arg::new("verbose")
                .short('v')
                .long("verbose")
                .about("configure logging level to use")
                .takes_value(true)
                .value_name("LEVEL")
                .possible_values(&LOGGING_LEVELS)
                .default_value(LOGGING_LEVELS[2])
                .global(true),
        )
        .subcommand(
            App::new("disassemble")
                .about("Disassemble a RISC-V ELF binary")
                .arg(
                    Arg::new("input-file")
                        .value_name("FILE")
                        .about("Binary file to be disassembled")
                        .takes_value(true)
                        .required(true),
                ),
        )
        .subcommand(
            App::new("cfg")
                .about("Generate control flow graph from RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .about("Source RISC-U binary to be analyzed")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("output-file")
                        .about("Output file to write to")
                        .short('o')
                        .long("output-file")
                        .takes_value(true)
                        .value_name("FILE")
                        .default_value("cfg.dot"),
                )
                .arg(
                    Arg::new("distances")
                        .about("Compute also shortest path distances from exit")
                        .short('d')
                        .long("distances"),
                ),
        )
        .subcommand(
            App::new("execute")
                .about("Symbolically execute a RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .about("RISC-U ELF binary to be executed")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("solver")
                        .about("SMT solver")
                        .short('s')
                        .long("solver")
                        .takes_value(true)
                        .value_name("SOLVER")
                        .possible_values(&SOLVER)
                        .default_value(SOLVER[0]),
                )
                .arg(
                    Arg::new("max-execution-depth")
                        .about("Number of instructions, where the path execution will be aborted")
                        .short('d')
                        .long("execution-depth")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", DEFAULT_MAX_EXECUTION_DEPTH))
                        .validator(is_u64),
                )
                .arg(
                    Arg::new("memory")
                        .about("Amount of memory to be used per execution context in megabytes [possible_values: 1 .. 1024]")
                        .short('m')
                        .long("memory")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", DEFAULT_MEMORY_SIZE.0 / bytesize::MB))
                        .validator(is_valid_memory_size),
                ),
        )
        .subcommand(
            App::new("rarity")
                .about("Performs rarity simulation on a RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .about("Source RISC-U binary to be analyzed")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("output-dir")
                        .about("Output directory to write round states to")
                        .short('o')
                        .long("output-dir")
                        .takes_value(true)
                        .value_name("DIR")
                        .default_value("states"),
                )
                .arg(
                    Arg::new("memory")
                        .about("Amount of memory to be used per execution context in megabytes [possible_values: 1 .. 1024]")
                        .short('m')
                        .long("memory")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("1")
                        .validator(is_valid_memory_size),
                )
                .arg(
                    Arg::new("cycles")
                        .about("Instructions to be executed for each round")
                        .short('c')
                        .long("cycles")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("1000")
                        .validator(is_u64),
                )
                .arg(
                    Arg::new("runs")
                        .about("Number of distinct runs")
                        .short('r')
                        .long("runs")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("3000")
                        .validator(is_u64),
                )
                .arg(
                    Arg::new("selection")
                    .about("Number of runs to select in every iteration")
                    .short('s')
                    .long("selection")
                    .takes_value(true)
                    .value_name("NUMBER")
                    .default_value("50")
                    .validator(is_u64))
                .arg(
                    Arg::new("iterations")
                    .about("Iterations of rarity simulation to run")
                    .short('i')
                    .long("iterations")
                    .takes_value(true)
                    .value_name("NUMBER")
                    .default_value("20")
                    .validator(is_u64))
                .arg(
                    Arg::new("copy-init-ratio")
                        .about("Determines how much new states are copied instead of started from the beginning")
                        .long("copy-init-ratio")
                        .takes_value(true)
                        .value_name("RATIO")
                        .default_value("0.6")
                        .validator(is_ratio)
                    )
        )
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .global_setting(AppSettings::GlobalVersion)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_matches<F>(a: Vec<&str>, f: F)
    where
        F: Fn(&ArgMatches),
    {
        let matches = args().try_get_matches_from(a.clone()).unwrap();

        f(matches.subcommand_matches(a[1]).unwrap())
    }

    #[test]
    fn test_execute_defaults_are_set() {
        with_matches(vec!["monster", "execute", "file.o"], |m| {
            assert!(m.is_present("memory"), "Default memory size is set");
            assert!(
                m.is_present("max-execution-depth"),
                "Default execution depth is set"
            );
            assert!(m.is_present("solver"), "Default solver is set");
        });
    }

    #[test]
    fn test_execute_memory_size_argument() {
        assert!(
            args()
                .try_get_matches_from(vec!["monster", "execute", "-m", "0", "file.o"])
                .is_err(),
            "Memory size 0 is invalid"
        );

        assert!(
            args()
                .try_get_matches_from(vec!["monster", "execute", "-m", "-23424", "file.o"])
                .is_err(),
            "Negative memory size is invalid"
        );

        assert!(
            args()
                .try_get_matches_from(vec!["monster", "execute", "-m", "23424", "file.o"])
                .is_err(),
            "memory size is invalid (out of range)"
        );
    }
}

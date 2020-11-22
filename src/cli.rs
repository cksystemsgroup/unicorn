use anyhow::Result;
use clap::{app_from_crate, App, AppSettings, Arg, ArgMatches};

pub const LOGGING_LEVELS: [&str; 5] = ["trace", "debug", "info", "warn", "error"];
pub const SOLVER: [&str; 3] = ["monster", "boolector", "z3"];

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

pub fn args() -> App<'static> {
    app_from_crate!(", ")
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
                        .default_value("1000")
                        .validator(is_u64),
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
                ),
        )
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .global_setting(AppSettings::GlobalVersion)
}

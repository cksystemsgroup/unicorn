use anyhow::{anyhow, Context, Result};
use bytesize::ByteSize;
use clap::{crate_authors, crate_description, crate_version, Arg, ArgMatches, Command};
use const_format::formatcp;
use std::str::FromStr;
use strum::{EnumString, EnumVariantNames, IntoStaticStr, VariantNames};
use unicorn::solver::SmtType;

#[derive(Debug, PartialEq, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

const MEMORY_SIZE: ByteSize = ByteSize(bytesize::MIB);

pub fn args() -> Command<'static> {
    Command::new("Unicorn")
        .version(crate_version!())
        .author(crate_authors!(", "))
        .about(crate_description!())
        .arg(
            Arg::new("verbose")
                .short('v')
                .long("verbose")
                .help("configure logging level to use")
                .takes_value(true)
                .value_name("LEVEL")
                .possible_values(LogLevel::VARIANTS)
                .default_value(LogLevel::Info.into())
                .global(true),
        )
        .subcommand(
            Command::new("disassemble")
                .about("Disassemble a RISC-V ELF binary")
                .arg(
                    Arg::new("input-file")
                        .value_name("FILE")
                        .help("Binary file to be disassembled")
                        .takes_value(true)
                        .required(true),
                ),
        )
        .subcommand(
            Command::new("beator")
                .about("Create a BTOR2 model for a RISC-U ELF binary")
                .arg(
                    Arg::new("bitblast")
                    .help("Perform bitblasting of the model")
                    .short('b')
                    .long("bitblast")
                )
                .arg(
                    Arg::new("dimacs")
                    .help("Output DIMACS CNF instead of BTOR2")
                    .short('d')
                    .long("dimacs")
                )
                .arg(
                    Arg::new("incremental-opt")
                    .help("Incremental optimization during unrolling")
                    .short('i')
                    .long("incremental")
                )
                .arg(
                    Arg::new("input-file")
                        .help("RISC-U ELF binary to be converted")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("max-heap")
                        .help("Number of machine-words usable as heap")
                        .long("max-heap")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("8")
                        .validator(is::<u32>),
                )
                .arg(
                    Arg::new("max-stack")
                        .help("Number of machine-words usable as stack")
                        .long("max-stack")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("16")
                        .validator(is::<u32>),
                )
                .arg(
                    Arg::new("memory")
                        .help("Total size of memory in MiB [possible: 1 .. 1024]")
                        .long("memory")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", MEMORY_SIZE.0 / bytesize::MIB))
                        .validator(is_valid_memory_size),
                )
                .arg(
                    Arg::new("output-file")
                    .help("Output path for the generated BTOR2 file")
                    .short('o')
                    .long("out")
                    .takes_value(true)
                )
                .arg(
                    Arg::new("prune-model")
                    .help("Prunes sequential part from model")
                    .short('p')
                    .long("prune")
                )
                .arg(
                    Arg::new("solver")
                        .help("SMT solver used for optimization")
                        .short('s')
                        .long("solver")
                        .takes_value(true)
                        .value_name("SOLVER")
                        .possible_values(SmtType::VARIANTS)
                        .default_value(SmtType::Generic.into()),
                )
                .arg(
                    Arg::new("unroll-model")
                    .help("Number of instructions to unroll from model")
                    .short('u')
                    .long("unroll")
                    .takes_value(true)
                    .value_name("NUMBER")
                    .validator(is::<usize>),
                )
        )
        .subcommand(
            Command::new("qubot")
                .about("Create a QUBO model for a RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("RISC-U ELF binary to be converted")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("output-file")
                    .help("Output path for the generated QUBO model")
                    .short('o')
                    .long("out")
                    .takes_value(true)
                )
                .arg(
                    Arg::new("max-heap")
                        .help("Number of machine-words usable as heap")
                        .long("max-heap")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("8")
                        .validator(is::<u32>),
                )
                .arg(
                    Arg::new("max-stack")
                        .help("Number of machine-words usable as stack")
                        .long("max-stack")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("16")
                        .validator(is::<u32>),
                )
                .arg(
                    Arg::new("memory")
                        .help("Total size of memory in MiB [possible: 1 .. 1024]")
                        .long("memory")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", MEMORY_SIZE.0 / bytesize::MIB))
                        .validator(is_valid_memory_size),
                )
                .arg(
                    Arg::new("input")
                    .help("Provide inputs to evaluate the model, separate by commas the values for a single instance, and with semicolon for various instances.")
                    .short('i')
                    .long("inputs")
                    .takes_value(true)
                )
                .arg(
                    Arg::new("solver")
                        .help("SMT solver used for optimization")
                        .short('s')
                        .long("solver")
                        .takes_value(true)
                        .value_name("SOLVER")
                        .possible_values(SmtType::VARIANTS)
                        .default_value(SmtType::Generic.into()),
                )
                .arg(
                    Arg::new("unroll-model")
                    .help("Number of instructions to unroll from model")
                    .short('u')
                    .long("unroll")
                    .takes_value(true)
                    .value_name("NUMBER")
                    .validator(is::<usize>),
                )

        )

        .subcommand(
            Command::new("dwave")
                .about("Execute QUBO model on the quantum annealer")
                .arg(
                    Arg::new("input-file")
                        .help("file generated by subcommand qubot")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("num-runs")
                        .help("number of samples to perform on the quantum annealer")
                        .long("num-runs")
                        .short('r')
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("1000")
                        .validator(is::<u32>),
                )
                .arg(
                    Arg::new("chain-strength")
                        .help("chain strength of physical variables to represent logic variables")
                        .long("chain-strength")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value("1.0")
                        .validator(is::<f32>),
                )

        )
        .subcommand_required(true)
        .arg_required_else_help(true)
        .propagate_version(true)
}

pub fn expect_arg<T: FromStr>(m: &ArgMatches, arg: &str) -> Result<T>
where
    <T as FromStr>::Err: Send + Sync + std::error::Error + 'static,
{
    m.value_of(arg)
        .ok_or_else(|| anyhow!("argument \"{}\" has to be set in CLI at all times", arg))
        .and_then(|s| {
            T::from_str(s).with_context(|| format!("argument \"{}\" has wrong format", arg))
        })
}

pub fn expect_optional_arg<T: FromStr>(m: &ArgMatches, arg: &str) -> Result<Option<T>>
where
    <T as FromStr>::Err: Send + Sync + std::error::Error + 'static,
{
    match m.value_of(arg) {
        Some(s) => {
            let res =
                T::from_str(s).with_context(|| format!("argument \"{}\" has wrong format", arg))?;
            Ok(Some(res))
        }
        None => Ok(None),
    }
}

fn is<T: FromStr>(v: &str) -> Result<(), String>
where
    <T as FromStr>::Err: std::fmt::Display,
{
    v.parse::<T>().map(|_| ()).map_err(|e| e.to_string())
}

fn is_valid_memory_size(v: &str) -> Result<(), String> {
    is::<u64>(v).and_then(|_| {
        let memory_size = v.parse::<u64>().expect("have checked that already");

        let valid_range = 1_u64..=1024_u64;

        if valid_range.contains(&memory_size) {
            Ok(())
        } else {
            Err(String::from("memory size has to be in range: 1 - 1024"))
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_matches<F>(a: Vec<&str>, f: F)
    where
        F: Fn(&ArgMatches),
    {
        let matches = args().get_matches_from(a.clone());

        f(matches.subcommand_matches(a[1]).unwrap())
    }

    #[test]
    fn test_execute_defaults_are_set() {
        with_matches(vec!["unicorn", "beator", "file.o"], |m| {
            assert!(m.is_present("memory"), "Default memory size is set");
            assert!(m.is_present("solver"), "Default solver is set");
        });
    }

    #[test]
    fn test_execute_memory_size_argument() {
        assert!(
            args()
                .try_get_matches_from(vec!["unicorn", "beator", "-m", "0", "file.o"])
                .is_err(),
            "Memory size 0 is invalid"
        );

        assert!(
            args()
                .try_get_matches_from(vec!["unicorn", "beator", "-m", "-23424", "file.o"])
                .is_err(),
            "Negative memory size is invalid"
        );

        assert!(
            args()
                .try_get_matches_from(vec!["unicorn", "beator", "-m", "23424", "file.o"])
                .is_err(),
            "memory size is invalid (out of range)"
        );
    }

    #[test]
    fn test_filename_argument_postitions() {
        assert!(
            args()
                .try_get_matches_from(vec!["unicorn", "beator", "-s", "generic", "file.o"])
                .is_ok(),
            "Input file can be declared after flags"
        );

        assert!(
            args()
                .try_get_matches_from(vec!["unicorn", "beator", "filename", "-s", "generic"])
                .is_ok(),
            "Input file can be declared before flags"
        );
    }
}

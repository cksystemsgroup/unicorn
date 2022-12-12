use anyhow::{anyhow, Context, Result};
use clap::{
    crate_authors, crate_description, crate_version, value_parser, Arg, ArgMatches, Command,
};
use std::str::FromStr;
use strum::{EnumString, EnumVariantNames, IntoStaticStr, VariantNames};

#[derive(Debug, PartialEq, Eq, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

#[derive(Debug, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum SmtType {
    Generic,
    #[cfg(feature = "boolector")]
    Boolector,
    #[cfg(feature = "z3")]
    Z3,
}

const DEFAULT_MEMORY_SIZE: &str = "1"; // 1 MiB
const DEFAULT_MAX_HEAP: &str = "8"; // 8 words
const DEFAULT_MAX_STACK: &str = "32"; // 32 words

pub fn args() -> Command {
    Command::new("Unicorn")
        .version(crate_version!())
        .author(crate_authors!(", "))
        .about(crate_description!())
        .arg(
            Arg::new("verbose")
                .short('v')
                .long("verbose")
                .help("configure logging level to use")
                .num_args(1)
                .value_name("LEVEL")
                .value_parser(value_parser_log_level())
                .default_value(Into::<&str>::into(LogLevel::Info))
                .global(true),
        )
        .subcommand(
            Command::new("emulate")
                .about("Emulate execution of a RISC-V ELF binary")
                .arg(
                    Arg::new("input-file")
                        .value_name("FILE")
                        .help("Binary file to be executed")
                        .num_args(1)
                        .required(true),
                )
                .arg(
                    Arg::new("memory")
                        .help("Total size of memory in MiB [possible: 1 .. 1024]")
                        .long("memory")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value(DEFAULT_MEMORY_SIZE)
                        .value_parser(value_parser_memory_size()),
                )
                .arg(
                    Arg::new("extras")
                        .help("Arguments passed to emulated program")
                        .value_name("ARGUMENTS")
                        .last(true)
                        .allow_hyphen_values(true)
                        .num_args(1..)
                ),
        )
        .subcommand(
            Command::new("disassemble")
                .about("Disassemble and print a RISC-V ELF binary")
                .arg(
                    Arg::new("input-file")
                        .value_name("FILE")
                        .help("Binary file to be disassembled")
                        .num_args(1)
                        .required(true),
                ),
        )
        .subcommand(
            Command::new("beator")
                .about("Create a BTOR2 model for a RISC-V ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("RISC-V ELF binary to be converted")
                        .num_args(1)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("bitblast")
                        .help("Perform bitblasting of the model")
                        .short('b')
                        .long("bitblast")
                        .num_args(0)
                )
                .arg(
                    Arg::new("dimacs")
                        .help("Output DIMACS CNF instead of BTOR2")
                        .short('d')
                        .long("dimacs")
                        .num_args(0)
                )
                .arg(
                    Arg::new("emulate")
                        .help("Start emulation from created model")
                        .short('e')
                        .long("emulate")
                        .num_args(0)
                )
                .arg(
                    Arg::new("compile")
                        .help("Compile program from created model")
                        .short('c')
                        .long("compile")
                        .num_args(0)
                )
                .arg(
                    Arg::new("discretize-memory")
                        .help("Discretize memory (don't use array logic)")
                        .long("discretize-memory")
                        .num_args(0)
                )
                .arg(
                    Arg::new("fast-minimize")
                        .help("Skip solver during graph minimization")
                        .long("fast-minimize")
                        .num_args(0)
                )
                .arg(
                    Arg::new("max-heap")
                        .help("Number of machine-words usable as heap")
                        .long("max-heap")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value(DEFAULT_MAX_HEAP)
                        .value_parser(value_parser!(u32)),
                )
                .arg(
                    Arg::new("max-stack")
                        .help("Number of machine-words usable as stack")
                        .long("max-stack")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value(DEFAULT_MAX_STACK)
                        .value_parser(value_parser!(u32)),
                )
                .arg(
                    Arg::new("memory")
                        .help("Total size of memory in MiB [possible: 1 .. 1024]")
                        .long("memory")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value(DEFAULT_MEMORY_SIZE)
                        .value_parser(value_parser_memory_size()),
                )
                .arg(
                    Arg::new("inputs")
                        .help("Concrete inputs to specialize the model")
                        .short('i')
                        .long("inputs")
                        .num_args(1)
                )
                .arg(
                    Arg::new("output-file")
                        .help("Output path for the generated BTOR2 file")
                        .short('o')
                        .long("out")
                        .num_args(1)
                )
                .arg(
                    Arg::new("prune-model")
                        .help("Prunes sequential part from model")
                        .short('p')
                        .long("prune")
                        .num_args(0)
                )
                .arg(
                    Arg::new("solver")
                        .help("SMT solver used for optimization")
                        .short('s')
                        .long("solver")
                        .num_args(1)
                        .value_name("SOLVER")
                        .value_parser(value_parser_smt_type())
                        .default_value(Into::<&str>::into(SmtType::Generic)),
                )
                .arg(
                    Arg::new("solver-timeout")
                        .help("Timeout for each SMT solver query in milliseconds")
                        .short('t')
                        .long("timeout")
                        .num_args(1)
                        .value_name("NUMBER")
                        .value_parser(value_parser!(u64)),
                )
                .arg(
                    Arg::new("unroll-model")
                        .help("Number of instructions to unroll from model")
                        .short('u')
                        .long("unroll")
                        .num_args(1)
                        .value_name("NUMBER")
                        .value_parser(value_parser!(usize)),
                )
                .arg(
                    Arg::new("from-btor2")
                        .help("Pass this flag if the input file is a BTOR2 file.")
                        .short('f')
                        .long("from-btor2")
                        .num_args(0)
                )
                .arg(
                    Arg::new("extras")
                        .help("Arguments passed to emulated program")
                        .value_name("ARGUMENTS")
                        .last(true)
                        .allow_hyphen_values(true)
                        .num_args(1..)
                )
        )
        .subcommand(
            Command::new("qubot")
                .about("Create a QUBO model for a RISC-V ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("If --from-btor2 flag is not passed, then RISC-V ELF binary to be converted, else a BTOR2 file.")
                        .num_args(1)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("from-btor2")
                        .help("Pass this flag if the input file is a BTOR2 file.")
                        .short('f')
                        .long("from-btor2")
                        .num_args(0)
                )
                .arg(
                    Arg::new("output-file")
                        .help("Output path for the generated QUBO model")
                        .short('o')
                        .long("out")
                        .num_args(1)
                )
                .arg(
                    Arg::new("max-heap")
                        .help("Number of machine-words usable as heap")
                        .long("max-heap")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value(DEFAULT_MAX_HEAP)
                        .value_parser(value_parser!(u32)),
                )
                .arg(
                    Arg::new("max-stack")
                        .help("Number of machine-words usable as stack")
                        .long("max-stack")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value(DEFAULT_MAX_STACK)
                        .value_parser(value_parser!(u32)),
                )
                .arg(
                    Arg::new("memory")
                        .help("Total size of memory in MiB [possible: 1 .. 1024]")
                        .long("memory")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value(DEFAULT_MEMORY_SIZE)
                        .value_parser(value_parser_memory_size()),
                )
                .arg(
                    Arg::new("inputs")
                        .help("Provide inputs to evaluate the model, separate by commas the values for a single instance, and with semicolon for various instances.")
                        .short('i')
                        .long("inputs")
                        .num_args(1)
                )
                .arg(
                    Arg::new("solver")
                        .help("SMT solver used for optimization")
                        .short('s')
                        .long("solver")
                        .num_args(1)
                        .value_name("SOLVER")
                        .value_parser(value_parser_smt_type())
                        .default_value(Into::<&str>::into(SmtType::Generic)),
                )
                .arg(
                    Arg::new("solver-timeout")
                        .help("Timeout for each SMT solver query in milliseconds")
                        .short('t')
                        .long("timeout")
                        .num_args(1)
                        .value_name("NUMBER")
                        .value_parser(value_parser!(u64)),
                )
                .arg(
                    Arg::new("unroll-model")
                        .help("Number of instructions to unroll from model")
                        .short('u')
                        .long("unroll")
                        .num_args(1)
                        .value_name("NUMBER")
                        .value_parser(value_parser!(usize)),
                )
                .arg(
                    Arg::new("ising")
                        .help("Makes qubot output an ising model")
                        .short('I')
                        .long("ising")
                        .num_args(0)
                )
                .arg(
                    Arg::new("from-dimacs")
                        .help("Consume DIMACS instead of RISC-V inputs")
                        .long("from-dimacs")
                        .num_args(0)
                )
                .arg(
                    Arg::new("extras")
                        .help("Arguments passed to emulated program")
                        .value_name("ARGUMENTS")
                        .last(true)
                        .allow_hyphen_values(true)
                        .num_args(1..)
                )
        )
        .subcommand(
            Command::new("dwave")
                .about("Execute QUBO model on the quantum annealer")
                .arg(
                    Arg::new("input-file")
                        .help("file generated by subcommand qubot")
                        .num_args(1)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("num-runs")
                        .help("number of samples to perform on the quantum annealer")
                        .short('r')
                        .long("num-runs")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value("1000")
                        .value_parser(value_parser!(u32)),
                )
                .arg(
                    Arg::new("chain-strength")
                        .help("chain strength of physical variables to represent logic variables")
                        .long("chain-strength")
                        .num_args(1)
                        .value_name("NUMBER")
                        .default_value("1.0")
                        .value_parser(value_parser!(f32)),
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
    m.get_one::<String>(arg)
        .ok_or_else(|| anyhow!("argument \"{}\" has to be set in CLI at all times", arg))
        .and_then(|s| {
            T::from_str(s).with_context(|| format!("argument \"{}\" has wrong format", arg))
        })
}

pub fn expect_optional_arg<T: FromStr>(m: &ArgMatches, arg: &str) -> Result<Option<T>>
where
    <T as FromStr>::Err: Send + Sync + std::error::Error + 'static,
{
    match m.get_one::<String>(arg) {
        Some(s) => {
            let res =
                T::from_str(s).with_context(|| format!("argument \"{}\" has wrong format", arg))?;
            Ok(Some(res))
        }
        None => Ok(None),
    }
}

pub fn collect_arg_values(m: &ArgMatches, arg: &str) -> Vec<String> {
    match m.get_many::<String>(arg) {
        Some(iter) => iter.map(|it| it.into()).collect(),
        None => vec![],
    }
}

fn value_parser_memory_size() -> clap::builder::RangedU64ValueParser {
    value_parser!(u64).range(1_u64..=1024_u64)
}

fn value_parser_log_level() -> clap::builder::PossibleValuesParser {
    clap::builder::PossibleValuesParser::new(LogLevel::VARIANTS)
}

fn value_parser_smt_type() -> clap::builder::PossibleValuesParser {
    clap::builder::PossibleValuesParser::new(SmtType::VARIANTS)
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
            assert!(m.contains_id("memory"), "Default memory size is set");
            assert!(m.contains_id("solver"), "Default solver is set");
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

use anyhow::{anyhow, Context, Result};
use clap::{crate_authors, crate_description, crate_version, App, AppSettings, Arg, ArgMatches};
use const_format::formatcp;
use lazy_static::lazy_static;
use monster::{
    engine::{
        rarity_simulation::{defaults as rarity_defaults, MeanType},
        symbolic_execution::defaults as symbolic_defaults,
    },
    path_exploration::ExplorationStrategyType,
    solver::{SmtType, SolverType},
};
use std::str::FromStr;
use strum::{EnumString, EnumVariantNames, IntoStaticStr, VariantNames};

#[derive(Debug, PartialEq, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

lazy_static! {
    static ref COPY_INIT_RATIO: String = format!("{}", rarity_defaults::COPY_INIT_RATIO);
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
                .help("configure logging level to use")
                .takes_value(true)
                .value_name("LEVEL")
                .possible_values(LogLevel::VARIANTS)
                .default_value(LogLevel::Info.into())
                .global(true),
        )
        .subcommand(
            App::new("disassemble")
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
            App::new("cfg")
                .about("Generate control flow graph from RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("Source RISC-U binary to be analyzed")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("output-file")
                        .help("Output file to write to")
                        .short('o')
                        .long("output-file")
                        .takes_value(true)
                        .value_name("FILE")
                        .default_value("cfg.dot"),
                )
                .arg(
                    Arg::new("distances")
                        .help("Compute also shortest path distances from exit")
                        .short('d')
                        .long("distances"),
                ),
        )
        .subcommand(
            App::new("execute")
                .about("Symbolically execute a RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("RISC-U ELF binary to be executed")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("solver")
                        .help("SMT solver")
                        .short('s')
                        .long("solver")
                        .takes_value(true)
                        .value_name("SOLVER")
                        .possible_values(SolverType::VARIANTS)
                        .default_value(SolverType::Monster.into()),
                )
                .arg(
                    Arg::new("max-execution-depth")
                        .help("Number of instructions, where the path execution will be aborted")
                        .short('d')
                        .long("execution-depth")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", symbolic_defaults::MAX_EXECUTION_DEPTH))
                        .validator(is::<u64>),
                )
                .arg(
                    Arg::new("memory")
                        .help("Amount of memory to be used per execution context in megabytes [possible_values: 1 .. 1024]")
                        .short('m')
                        .long("memory")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", symbolic_defaults::MEMORY_SIZE.0 / bytesize::MIB))
                        .validator(is_valid_memory_size),
                )
                .arg(
                    Arg::new("strategy")
                    .help("Path exploration strategy to use when exploring state search space")
                    .long("strategy")
                    .takes_value(true)
                    .value_name("STRATEGY")
                    .default_value(ExplorationStrategyType::ShortestPaths.into())
                    .possible_values(ExplorationStrategyType::VARIANTS)
                ),
        )
        .subcommand(
            App::new("model")
                .about("Create a BTOR2 model for a RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("RISC-U ELF binary to be converted")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
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
            App::new("smt")
                .about("Create an SMT-LIB file for a RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("RISC-U ELF binary to be converted")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("max-execution-depth")
                        .help("Number of instructions, where the path execution will be aborted")
                        .short('d')
                        .long("execution-depth")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", symbolic_defaults::MAX_EXECUTION_DEPTH))
                        .validator(is::<u64>),
                )
                .arg(
                    Arg::new("memory")
                        .help("Amount of memory to be used per execution context in megabytes [possible_values: 1 .. 1024]")
                        .short('m')
                        .long("memory")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", symbolic_defaults::MEMORY_SIZE.0 / bytesize::MIB))
                        .validator(is_valid_memory_size),
                )
                .arg(
                    Arg::new("strategy")
                    .help("Path exploration strategy to use when exploring state search space")
                    .long("strategy")
                    .takes_value(true)
                    .value_name("STRATEGY")
                    .default_value(ExplorationStrategyType::ShortestPaths.into())
                    .possible_values(ExplorationStrategyType::VARIANTS)
                )
                .arg(
                    Arg::new("smt-type")
                    .help("Specify a solver type to generate the SMT file for")
                    .long("smt-type")
                    .short('t')
                    .takes_value(true)
                    .default_value(SmtType::Generic.into())
                    .possible_values(SmtType::VARIANTS)
                )
                .arg(
                    Arg::new("output-file")
                    .help("Output path for the generated SMT-LIB file")
                    .short('o')
                    .long("out")
                    .takes_value(true)
                )
        )
        .subcommand(
            App::new("rarity")
                .about("Performs rarity simulation on a RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .help("Source RISC-U binary to be analyzed")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("memory")
                        .help("Amount of memory to be used per execution context in megabytes [possible_values: 1 .. 1024]")
                        .short('m')
                        .long("memory")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", rarity_defaults::MEMORY_SIZE.0 / bytesize::MIB))
                        .validator(is_valid_memory_size),
                )
                .arg(
                    Arg::new("step-size")
                        .help("Instructions to be executed for each round")
                        .long("step-size")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", rarity_defaults::STEP_SIZE))
                        .validator(is::<u64>),
                )
                .arg(
                    Arg::new("states")
                        .help("Number of distinct states")
                        .long("states")
                        .takes_value(true)
                        .value_name("NUMBER")
                        .default_value(formatcp!("{}", rarity_defaults::AMOUNT_OF_STATES))
                        .validator(is::<usize>),
                )
                .arg(
                    Arg::new("selection")
                    .help("Number of runs to select in every iteration")
                    .short('s')
                    .long("selection")
                    .takes_value(true)
                    .value_name("NUMBER")
                    .default_value(formatcp!("{}", rarity_defaults::SELECTION))
                    .validator(is::<usize>))
                .arg(
                    Arg::new("iterations")
                    .help("Iterations of rarity simulation to run")
                    .short('i')
                    .long("iterations")
                    .takes_value(true)
                    .value_name("NUMBER")
                    .default_value(formatcp!("{}", rarity_defaults::ITERATIONS))
                    .validator(is::<u64>))
                .arg(
                    Arg::new("copy-init-ratio")
                        .help("Determines how much new states are copied instead of started from the beginning")
                        .long("copy-init-ratio")
                        .takes_value(true)
                        .value_name("RATIO")
                        .default_value(COPY_INIT_RATIO.as_str())
                        .validator(is_ratio)
                    )
                .arg(
                    Arg::new("mean")
                    .help("The average to be used for the counts")
                    .long("mean")
                    .takes_value(true)
                    .value_name("MEAN")
                    .possible_values(MeanType::VARIANTS)
                    .default_value(rarity_defaults::MEAN_TYPE.into())
                    )
        )
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .global_setting(AppSettings::PropagateVersion)
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

    #[test]
    fn test_filename_argument_postitions() {
        assert!(
            args()
                .try_get_matches_from(vec!["monster", "smt", "-t", "generic", "file.o"])
                .is_ok(),
            "Input file can be declared after flags"
        );

        assert!(
            args()
                .try_get_matches_from(vec!["monster", "smt", "filename", "-t", "generic"])
                .is_ok(),
            "Input file can be declared before flags"
        );
    }
}

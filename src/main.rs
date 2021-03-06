mod cli;

use anyhow::{Context, Result};
use bytesize::ByteSize;
use cli::{expect_arg, LogLevel};
use env_logger::{Env, TimestampPrecision};
use log::info;
use monster::{
    disassemble::disassemble,
    engine::{self, EngineOptions},
    execute_elf_with,
    path_exploration::{ControlFlowGraph, ShortestPathStrategy},
    rarity::{self, MetricType},
    solver::{self, SolverType},
};
use riscu::load_object_file;
use std::{
    env,
    fmt::Display,
    fs::File,
    io::Write,
    path::{Path, PathBuf},
    str::FromStr,
};

fn main() -> Result<()> {
    let matches = cli::args().get_matches();

    // process global flags
    let log_level = expect_arg::<LogLevel>(&matches, "verbose")?;

    init_logger(log_level)?;

    // process subcommands
    match matches.subcommand() {
        ("disassemble", Some(args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;

            disassemble(input)
        }
        ("cfg", Some(args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let output = expect_arg::<PathBuf>(args, "output-file")?;
            let distances = args.is_present("distances");

            let program = load_object_file(input)?;

            if distances {
                let strat = ShortestPathStrategy::compute_for(&program)?;

                write_to_file(output, &strat)
            } else {
                let cfg = ControlFlowGraph::build_for(&program)?;

                write_to_file(output, &cfg)
            }
        }
        ("execute", Some(args)) => {
            let input = expect_arg::<PathBuf>(&args, "input-file")?;
            let solver = expect_arg::<SolverType>(&args, "solver")?;
            let depth = expect_arg::<u64>(args, "max-execution-depth")?;
            let megabytes = expect_arg::<u64>(args, "memory")?;

            let options = EngineOptions {
                max_exection_depth: depth,
                memory_size: ByteSize::mb(megabytes),
            };

            let program = load_object_file(&input)?;

            let strategy = ShortestPathStrategy::compute_for(&program)?;

            if let Some(bug) = match solver {
                SolverType::Monster => execute_elf_with(
                    &input,
                    &options,
                    &strategy,
                    &solver::MonsterSolver::default(),
                ),
                SolverType::External => execute_elf_with(
                    &input,
                    &options,
                    &strategy,
                    &solver::ExternalSolver::default(),
                ),
                #[cfg(feature = "boolector")]
                SolverType::Boolector => {
                    execute_elf_with(&input, &options, &strategy, &solver::Boolector::default())
                }
                #[cfg(feature = "z3")]
                SolverType::Z3 => {
                    execute_elf_with(&input, &options, &strategy, &solver::Z3::default())
                }
            }
            .with_context(|| format!("Execution of {} failed", input.display()))?
            {
                info!("bug found:\n{}", bug);
            } else {
                info!("no bug found in binary");
            };

            Ok(())
        }
        ("rarity", Some(args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let megabytes = expect_arg::<u64>(args, "memory")?;
            let cycles = expect_arg::<u64>(args, "cycles")?;
            let iterations = expect_arg::<u64>(args, "iterations")?;
            let runs = expect_arg::<u64>(args, "runs")?;
            let selection = expect_arg::<u64>(args, "selection")?;
            let copy_ratio = expect_arg::<f64>(args, "copy-init-ratio")?;
            let metric = expect_arg::<MetricType>(args, "metric")?;

            if let Some(bug) = rarity::execute(
                input,
                ByteSize::mb(megabytes),
                runs,
                selection,
                cycles,
                iterations,
                copy_ratio,
                metric,
            )? {
                info!("bug found:\n{}", bug);
            } else {
                info!("no bug found in binary");
            }

            Ok(())
        }
        _ => unreachable!(),
    }
}

fn init_logger(cli_log_level: LogLevel) -> Result<()> {
    let log_level_env_var = "MONSTER_LOG";
    let log_style_env_var = "MONSTER_LOG_STYLE";

    let env = Env::new()
        .filter_or::<&'static str, &'static str>(log_level_env_var, (&cli_log_level).into())
        .write_style_or(log_style_env_var, "always");

    let mut builder = env_logger::Builder::from_env(env);

    builder.format_timestamp(Some(TimestampPrecision::Millis));

    let level = env::var(log_style_env_var)
        .map_err(|e| e.to_string())
        .and_then(|s| LogLevel::from_str(s.as_str()).map_err(|e| e.to_string()))
        .unwrap_or(cli_log_level);

    if level == LogLevel::Info {
        builder.format(|buf, record| writeln!(buf, "{}", record.args()));
    }

    builder.try_init().context("Failed to initialize logger")
}

fn write_to_file<P, O>(path: P, object: O) -> Result<()>
where
    P: AsRef<Path>,
    O: Display,
{
    File::create(path)
        .and_then(|mut f| write!(f, "{}", object).and_then(|_| f.sync_all()))
        .context("Failed to write control flow graph to file")?;

    Ok(())
}

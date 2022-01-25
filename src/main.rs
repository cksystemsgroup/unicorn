mod cli;
mod modeler;

use anyhow::{Context, Result};
use bytesize::ByteSize;
use cli::{expect_arg, expect_optional_arg, LogLevel};
use env_logger::{Env, TimestampPrecision};
use log::info;
use modeler::builder::generate_model;
use modeler::memory::replace_memory;
use modeler::optimize::optimize_model;
use modeler::solver::*;
use modeler::unroller::{renumber_model, unroll_model};
use modeler::write_model;
use monster::{
    disassemble::disassemble,
    generate_smt, generate_smt_to_file,
    path_exploration::{
        CoinFlipStrategy, ControlFlowGraph,
        ExplorationStrategyType::{self, CoinFlip, ShortestPaths},
        ShortestPathStrategy,
    },
    rarity_simulate_elf_with,
    solver::{
        self,
        SolverType::{self, Monster},
    },
    symbolically_execute_elf_with, RaritySimulationOptions, SmtGenerationOptions,
    SymbolicExecutionOptions,
};
use riscu::load_object_file;
use std::{
    env,
    fmt::Display,
    fs::File,
    io::{stdout, Write},
    path::{Path, PathBuf},
    str::FromStr,
};

#[cfg(feature = "boolector")]
use monster::solver::SolverType::Boolector;
#[cfg(feature = "z3")]
use monster::solver::SolverType::Z3;

fn main() -> Result<()> {
    let matches = cli::args().get_matches();

    // process global flags
    let log_level = expect_arg::<LogLevel>(&matches, "verbose")?;

    init_logger(log_level)?;

    // process subcommands
    match matches.subcommand() {
        Some(("disassemble", args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;

            disassemble(input)
        }
        Some(("cfg", args)) => {
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
        Some(("smt", args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let output = expect_optional_arg::<PathBuf>(args, "output-file")?;
            let strategy = expect_arg::<ExplorationStrategyType>(args, "strategy")?;
            let options = SmtGenerationOptions {
                max_execution_depth: expect_arg(args, "max-execution-depth")?,
                memory_size: ByteSize::mib(expect_arg(args, "memory")?),
                smt_type: expect_arg(args, "smt-type")?,
            };

            let program = load_object_file(&input)?;

            match strategy {
                ShortestPaths => {
                    let strategy = ShortestPathStrategy::compute_for(&program)?;

                    if let Some(file) = output {
                        generate_smt_to_file(&input, &file, &options, &strategy)
                    } else {
                        generate_smt(&input, stdout(), &options, &strategy)
                    }
                }
                CoinFlip => {
                    let strategy = CoinFlipStrategy::default();

                    if let Some(file) = output {
                        generate_smt_to_file(&input, &file, &options, &strategy)
                    } else {
                        generate_smt(&input, stdout(), &options, &strategy)
                    }
                }
            }
            .with_context(|| format!("Execution of {} failed", input.display()))
            .map(|(potential_bug, profile)| {
                info!("{}", profile);

                if let Some(bug) = potential_bug {
                    info!("bug found:\n{}", bug);
                }
            })
        }
        Some(("execute", args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let solver = expect_arg::<SolverType>(args, "solver")?;
            let strategy = expect_arg::<ExplorationStrategyType>(args, "strategy")?;
            let options = SymbolicExecutionOptions {
                max_exection_depth: expect_arg(args, "max-execution-depth")?,
                memory_size: ByteSize::mib(expect_arg(args, "memory")?),
                ..Default::default()
            };

            let program = load_object_file(&input)?;

            match (strategy, solver) {
                (ShortestPaths, Monster) => symbolically_execute_elf_with(
                    &input,
                    &options,
                    &ShortestPathStrategy::compute_for(&program)?,
                    &solver::MonsterSolver::default(),
                ),
                #[cfg(feature = "boolector")]
                (ShortestPaths, Boolector) => symbolically_execute_elf_with(
                    &input,
                    &options,
                    &ShortestPathStrategy::compute_for(&program)?,
                    &solver::Boolector::default(),
                ),
                #[cfg(feature = "z3")]
                (ShortestPaths, Z3) => symbolically_execute_elf_with(
                    &input,
                    &options,
                    &ShortestPathStrategy::compute_for(&program)?,
                    &solver::Z3::default(),
                ),
                (CoinFlip, Monster) => symbolically_execute_elf_with(
                    &input,
                    &options,
                    &CoinFlipStrategy::default(),
                    &solver::MonsterSolver::default(),
                ),
                #[cfg(feature = "boolector")]
                (CoinFlip, Boolector) => symbolically_execute_elf_with(
                    &input,
                    &options,
                    &CoinFlipStrategy::default(),
                    &solver::Boolector::default(),
                ),
                #[cfg(feature = "z3")]
                (CoinFlip, Z3) => symbolically_execute_elf_with(
                    &input,
                    &options,
                    &CoinFlipStrategy::default(),
                    &solver::Z3::default(),
                ),
            }
            .with_context(|| format!("Execution of {} failed", input.display()))
            .map(|(potential_bug, profile)| {
                info!("{}", profile);

                if let Some(bug) = potential_bug {
                    info!("bug found:\n{}", bug);
                } else {
                    info!("no bug found in binary");
                }
            })
        }
        Some(("model", args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let output = expect_optional_arg::<PathBuf>(args, "output-file")?;
            let unroll = expect_optional_arg(args, "unroll-model")?;
            let solver = expect_arg::<monster::SmtType>(args, "solver")?;
            let prune = args.is_present("prune-model");

            let program = load_object_file(&input)?;

            let mut model = generate_model(&program)?;
            if let Some(unroll_depth) = unroll {
                model.lines.clear();
                // TODO: Check if memory replacement is requested.
                replace_memory(&mut model);
                for n in 0..unroll_depth {
                    unroll_model(&mut model, n);
                    match solver {
                        monster::SmtType::Generic => {
                            optimize_model::<none_impl::NoneSolver>(&mut model)
                        }
                        #[cfg(feature = "boolector")]
                        monster::SmtType::Boolector => {
                            optimize_model::<boolector_impl::BoolectorSolver>(&mut model)
                        }
                        #[cfg(feature = "z3")]
                        monster::SmtType::Z3 => {
                            panic!("solver Z3 not supported yet")
                        }
                    }
                }
                renumber_model(&mut model, prune);
            }

            if let Some(output_path) = output {
                let file = File::create(output_path)?;
                write_model(&model, file)?;
            } else {
                write_model(&model, stdout())?;
            }

            Ok(())
        }
        Some(("rarity", args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;

            let options = RaritySimulationOptions {
                memory_size: ByteSize::mib(expect_arg(args, "memory")?),
                amount_of_states: expect_arg(args, "states")?,
                step_size: expect_arg(args, "step-size")?,
                selection: expect_arg(args, "selection")?,
                iterations: expect_arg(args, "iterations")?,
                copy_init_ratio: expect_arg(args, "copy-init-ratio")?,
                mean: expect_arg(args, "mean")?,
            };

            if let Some(bug) = rarity_simulate_elf_with(input, &options)? {
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

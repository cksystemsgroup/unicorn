mod cli;
mod unicorn;

use crate::unicorn::qubot::{InputEvaluator, Qubot};
use anyhow::{Context, Result};
use bytesize::ByteSize;
use cli::{expect_arg, expect_optional_arg, LogLevel};
use env_logger::{Env, TimestampPrecision};
use log::info;
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
use unicorn::bitblasting::BitBlasting;
use unicorn::bitblasting_printer::write_gate_model;
use unicorn::builder::generate_model;
use unicorn::memory::replace_memory;
use unicorn::optimize::optimize_model;
use unicorn::solver::*;
use unicorn::unroller::{prune_model, renumber_model, unroll_model};
use unicorn::write_model;

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
        Some(("unicorn", args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let output = expect_optional_arg::<PathBuf>(args, "output-file")?;
            let unroll = expect_optional_arg(args, "unroll-model")?;
            let solver = expect_arg::<monster::SmtType>(args, "solver")?;
            let max_heap = expect_arg::<u32>(args, "max-heap")?;
            let max_stack = expect_arg::<u32>(args, "max-stack")?;
            let memory_size = ByteSize::mib(expect_arg(args, "memory")?).as_u64();
            let prune = args.is_present("prune-model");
            let bitblast = args.is_present("bitblast");

            let program = load_object_file(&input)?;

            let mut model = generate_model(&program, memory_size, max_heap, max_stack)?;
            if let Some(unroll_depth) = unroll {
                model.lines.clear();
                // TODO: Check if memory replacement is requested.
                replace_memory(&mut model);
                for n in 0..unroll_depth {
                    unroll_model(&mut model, n);
                    optimize_model::<none_impl::NoneSolver>(&mut model)
                }
                if prune {
                    prune_model(&mut model);
                }
                match solver {
                    monster::SmtType::Generic => (), // nothing left to do
                    #[cfg(feature = "boolector")]
                    monster::SmtType::Boolector => {
                        optimize_model::<boolector_impl::BoolectorSolver>(&mut model)
                    }
                    #[cfg(feature = "z3")]
                    monster::SmtType::Z3 => {
                        optimize_model::<z3solver_impl::Z3SolverWrapper>(&mut model)
                    }
                }
            }

            if bitblast {
                info!("Finished building model, starting bitblasting");
                let mut bitblasting = BitBlasting::new(&model, true, 64);
                let bad_states = bitblasting.process_model(&model);
                if let Some(ref output_path) = output {
                    let file = File::create(output_path)?;
                    write_gate_model(&model, &bad_states, file)?;
                } else {
                    write_gate_model(&model, &bad_states, stdout())?;
                }
                // TODO: call_qubot(&bitblasting, &bad_states);
            } else {
                renumber_model(&mut model);
                if let Some(ref output_path) = output {
                    let file = File::create(output_path)?;
                    write_model(&model, file)?;
                } else {
                    write_model(&model, stdout())?;
                }
            }

            Ok(())
        }
        Some(("qubot", args)) => {
            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let output = expect_optional_arg::<PathBuf>(args, "output-file")?;
            let inputs = expect_optional_arg::<String>(args, "input")?;
            let unroll = expect_optional_arg(args, "unroll-model")?;
            let solver = expect_arg::<monster::SmtType>(args, "solver")?;

            let program = load_object_file(&input)?;

            // TODO: Unify "qubot" and "model" commands to get all options.
            let mut model = generate_model(&program, bytesize::MIB, 8, 16)?;

            if let Some(unroll_depth) = unroll {
                model.lines.clear();
                // TODO: Check if memory replacement is requested.
                replace_memory(&mut model);
                for n in 0..unroll_depth {
                    unroll_model(&mut model, n);
                    optimize_model::<none_impl::NoneSolver>(&mut model)
                }
                prune_model(&mut model);
                match solver {
                    monster::SmtType::Generic => (), // nothing left to do
                    #[cfg(feature = "boolector")]
                    monster::SmtType::Boolector => {
                        optimize_model::<boolector_impl::BoolectorSolver>(&mut model)
                    }
                    #[cfg(feature = "z3")]
                    monster::SmtType::Z3 => {
                        optimize_model::<z3solver_impl::Z3SolverWrapper>(&mut model)
                    }
                }
            }

            renumber_model(&mut model);
            let mut bitblasting = BitBlasting::new(&model, true, 64);
            let bad_states = bitblasting.process_model(&model);

            let mut qubot = Qubot::new(&bitblasting);
            let bad_state_qubits = qubot.build_qubo(&bad_states);
            if let Some(ref output_path) = output {
                let file = File::create(output_path)?;
                qubot.dump_model(file, bad_state_qubits.clone())?;
            }

            if let Some(all_inputs) = inputs {
                let total_variables = bitblasting.input_gates.len();
                let instances: Vec<&str> = all_inputs.split('-').collect();

                for instance in instances {
                    let mut values: Vec<i64> = instance
                        .split(',')
                        .map(|x| i64::from_str(x).unwrap())
                        .collect();

                    while values.len() < total_variables {
                        values.push(0);
                    }

                    let mut input_evaluator = InputEvaluator::new();
                    let (final_offset, true_bad_states) = input_evaluator.evaluate_inputs(
                        &qubot.qubo,
                        &qubot.mapping,
                        &bitblasting.input_gates,
                        &values,
                        bad_state_qubits.clone(),
                    );
                    println!("{} {}", final_offset, true_bad_states.len());
                }
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

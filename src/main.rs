mod cli;
mod quantum_annealing;
mod unicorn;

use crate::quantum_annealing::dwave_api::sample_quantum_annealer;
use crate::unicorn::bitblasting::bitblast_model;
use crate::unicorn::bitblasting_dimacs::write_dimacs_model;
use crate::unicorn::bitblasting_printer::write_btor2_model;
use crate::unicorn::builder::generate_model;
use crate::unicorn::memory::replace_memory;
use crate::unicorn::optimize::optimize_model;
use crate::unicorn::qubot::{InputEvaluator, Qubot};
use crate::unicorn::solver::*;
use crate::unicorn::unroller::{prune_model, renumber_model, unroll_model};
use crate::unicorn::write_model;

use ::unicorn::disassemble::disassemble;
use ::unicorn::SmtType;
use anyhow::{Context, Result};
use bytesize::ByteSize;
use cli::{expect_arg, expect_optional_arg, LogLevel};
use env_logger::{Env, TimestampPrecision};
use riscu::load_object_file;
use std::{
    env,
    fs::File,
    io::{stdout, Write},
    path::PathBuf,
    str::FromStr,
};

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
        Some(("beator", args)) | Some(("qubot", args)) => {
            let is_beator = matches.subcommand().unwrap().0 == "beator";

            let input = expect_arg::<PathBuf>(args, "input-file")?;
            let output = expect_optional_arg::<PathBuf>(args, "output-file")?;
            let unroll = expect_optional_arg(args, "unroll-model")?;
            let solver = expect_arg::<SmtType>(args, "solver")?;
            let max_heap = expect_arg::<u32>(args, "max-heap")?;
            let max_stack = expect_arg::<u32>(args, "max-stack")?;
            let memory_size = ByteSize::mib(expect_arg(args, "memory")?).as_u64();
            let incremental = is_beator && args.is_present("incremental-opt");
            let prune = !is_beator || args.is_present("prune-model");

            let program = load_object_file(&input)?;

            let mut model = generate_model(&program, memory_size, max_heap, max_stack)?;
            if let Some(unroll_depth) = unroll {
                model.lines.clear();
                // TODO: Check if memory replacement is requested.
                replace_memory(&mut model);
                for n in 0..unroll_depth {
                    unroll_model(&mut model, n);
                    if incremental {
                        optimize_model::<none_impl::NoneSolver>(&mut model)
                    }
                }
                if prune {
                    prune_model(&mut model);
                }

                match solver {
                    ::unicorn::SmtType::Generic => {
                        optimize_model::<none_impl::NoneSolver>(&mut model)
                    }
                    #[cfg(feature = "boolector")]
                    ::unicorn::SmtType::Boolector => {
                        optimize_model::<boolector_impl::BoolectorSolver>(&mut model)
                    }
                    #[cfg(feature = "z3")]
                    ::unicorn::SmtType::Z3 => {
                        optimize_model::<z3solver_impl::Z3SolverWrapper>(&mut model)
                    }
                }
            }

            if !is_beator || unroll.is_some() {
                renumber_model(&mut model);
            }

            if is_beator {
                let bitblast = args.is_present("bitblast");
                let dimacs = args.is_present("dimacs");

                if bitblast {
                    let gate_model = bitblast_model(&model, true, 64);
                    if let Some(ref output_path) = output {
                        let file = File::create(output_path)?;
                        if dimacs {
                            write_dimacs_model(&gate_model, file)?;
                        } else {
                            write_btor2_model(&gate_model, file)?;
                        }
                    } else if dimacs {
                        write_dimacs_model(&gate_model, stdout())?;
                    } else {
                        write_btor2_model(&gate_model, stdout())?;
                    }
                } else if let Some(ref output_path) = output {
                    let file = File::create(output_path)?;
                    write_model(&model, file)?;
                } else {
                    write_model(&model, stdout())?;
                }
            } else {
                let inputs = expect_optional_arg::<String>(args, "input")?;
                let gate_model = bitblast_model(&model, true, 64);

                let mut qubot = Qubot::new(&gate_model);
                let bad_state_qubits = qubot.build_qubo();
                if let Some(ref output_path) = output {
                    let file = File::create(output_path)?;
                    qubot.dump_model(file, bad_state_qubits.clone())?;
                }

                if let Some(all_inputs) = inputs {
                    let total_variables = gate_model.input_gates.len();
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
                            &gate_model.input_gates,
                            &values,
                            bad_state_qubits.clone(),
                        );
                        println!(
                            "offset:{}, bad states count:{}",
                            final_offset,
                            true_bad_states.len()
                        );
                    }
                }
            }

            Ok(())
        }
        Some(("dwave", args)) => {
            let input = expect_arg::<String>(args, "input-file")?;
            let runs = expect_arg::<u32>(args, "num-runs")?;
            let chain_strength = expect_arg::<f32>(args, "chain-strength")?;

            sample_quantum_annealer(&input, runs, chain_strength)
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

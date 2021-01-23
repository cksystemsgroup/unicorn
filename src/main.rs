mod cli;

use anyhow::{Context, Result};
use bytesize::ByteSize;
use cli::expect_arg;
use env_logger::{Env, TimestampPrecision};
use log::info;
use monster::{
    disassemble::disassemble,
    engine::{self, EngineOptions},
    execute_elf_with,
    path_exploration::{ControlFlowGraph, ShortestPathStrategy},
    rarity, solver,
};
use riscu::load_object_file;
use std::{env, fmt::Display, fs::File, io::Write, path::Path};

fn main() -> Result<()> {
    let matches = cli::args().get_matches();

    // process global flags
    let log_level = expect_arg(&matches, "verbose");

    init_logger(log_level)?;

    // process subcommands
    match matches.subcommand() {
        Some(("disassemble", args)) => {
            let input = Path::new(expect_arg(&args, "input-file"));

            disassemble(Path::new(input))
        }
        Some(("cfg", args)) => {
            let input = Path::new(expect_arg(&args, "input-file"));
            let output = Path::new(expect_arg(&args, "output-file"));
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
        Some(("execute", args)) => {
            let input = Path::new(expect_arg(&args, "input-file"));
            let solver = expect_arg(&args, "solver");

            let depth = args
                .value_of_t::<u64>("max-execution-depth")
                .expect("value is validated already");

            let megabytes = args
                .value_of_t::<u64>("memory")
                .expect("value is validated already");

            let options = EngineOptions {
                max_exection_depth: depth,
                memory_size: ByteSize::mb(megabytes),
            };

            let program = load_object_file(input)?;

            let strategy = ShortestPathStrategy::compute_for(&program)?;

            if let Some(bug) = match solver {
                "monster" => execute_elf_with(
                    input,
                    &options,
                    &strategy,
                    &solver::MonsterSolver::default(),
                ),
                "external" => execute_elf_with(
                    input,
                    &options,
                    &strategy,
                    &solver::ExternalSolver::default(),
                ),
                #[cfg(feature = "boolector-solver")]
                "boolector" => {
                    execute_elf_with(input, &options, &strategy, &solver::Boolector::default())
                }
                #[cfg(feature = "z3-solver")]
                "z3" => execute_elf_with(input, &options, &strategy, &solver::Z3::default()),
                _ => unreachable!(),
            }
            .with_context(|| format!("Execution of {} failed", input.display()))?
            {
                info!("bug found:\n{}", bug);
            } else {
                info!("no bug found in binary");
            };

            Ok(())
        }
        Some(("rarity", args)) => {
            let input = Path::new(expect_arg(&args, "input-file"));

            let megabytes = args
                .value_of_t::<u64>("memory")
                .expect("value is validated already");

            let cycles = args
                .value_of_t::<u64>("cycles")
                .expect("value is validated already");

            let iterations = args
                .value_of_t::<u64>("iterations")
                .expect("value is validated already");

            let runs = args
                .value_of_t::<u64>("runs")
                .expect("value is validated already");

            let selection = args
                .value_of_t::<u64>("selection")
                .expect("value is validated already");

            let copy_ratio = args
                .value_of_t::<f64>("copy-init-ratio")
                .expect("value is validated already");

            if let Some(bug) = rarity::execute(
                input,
                ByteSize::mb(megabytes),
                runs,
                selection,
                cycles,
                iterations,
                copy_ratio,
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

fn init_logger(cli_log_level: &str) -> Result<()> {
    let env = Env::new()
        .filter_or("MONSTER_LOG", cli_log_level)
        .write_style_or("MONSTER_LOG_STYLE", "always");

    let mut builder = env_logger::Builder::from_env(env);

    builder.format_timestamp(Some(TimestampPrecision::Millis));

    let level = env::var("MONSTER_LOG").unwrap_or_else(|_| cli_log_level.to_owned());

    if level == "info" {
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

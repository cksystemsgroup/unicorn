mod cli;

use anyhow::Result;
use bytesize::ByteSize;
use cli::expect_arg;
use env_logger::{Env, TimestampPrecision};
use monster::{
    cfg::{build_cfg_from_file, write_to_file},
    disassemble::disassemble,
    engine,
    exploration_strategy::ShortestPathStrategy,
};
use std::path::Path;

fn main() -> Result<()> {
    let matches = cli::args().get_matches();

    let log_level = expect_arg(&matches, "verbose");

    let env = Env::new()
        .filter_or("MONSTER_LOG", log_level)
        .write_style_or("MONSTER_LOG_STYLE", "always");

    env_logger::Builder::from_env(env)
        .format_timestamp(Some(TimestampPrecision::Millis))
        .init();

    match matches.subcommand() {
        Some(("disassemble", args)) => {
            let input = Path::new(expect_arg(&args, "input-file"));

            disassemble(Path::new(input))
        }
        Some(("cfg", args)) => {
            let input = Path::new(expect_arg(&args, "input-file"));
            let output = Path::new(expect_arg(&args, "output-file"));
            let distances = args.is_present("distances");

            let ((cfg, _), program) = build_cfg_from_file(Path::new(input))?;

            if distances {
                ShortestPathStrategy::new(&cfg, program.code.address)
                    .write_cfg_with_distances_to_file(output)
            } else {
                write_to_file(&cfg, output)
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

            engine::execute(
                input,
                match solver {
                    "monster" => engine::Backend::Monster,
                    "boolector" => engine::Backend::Boolector,
                    "z3" => engine::Backend::Z3,
                    _ => unreachable!(),
                },
                depth,
                ByteSize::mb(megabytes),
            )
        }
        _ => unreachable!(),
    }
}

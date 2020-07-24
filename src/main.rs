use clap::{App, Arg};
use std::path::Path;
use std::process;

mod compile;

use compile::compile_example;

fn main() {
    let args = App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS").replace(":", ", ").as_str())
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .arg(
            Arg::with_name("compile")
                .short('c')
                .long("compile")
                .value_name("FILE")
                .about("compile a source file")
                .takes_value(true)
                .required(true),
        )
        .get_matches();

    if let Some(source) = args.value_of("compile") {
        if let Err(e) = compile_example(Path::new(source)) {
            println!("{}", e);
            process::exit(1);
        }
    }
}

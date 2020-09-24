use clap::{crate_authors, crate_description, crate_name, crate_version, App, AppSettings, Arg};

pub fn args() -> App<'static> {
    App::new(crate_name!())
        .version(crate_version!())
        .author(crate_authors!(", "))
        .about(crate_description!())
        .subcommand(
            App::new("disassemble")
                .about("Disassemble a RISC-V ELF binary")
                .arg(
                    Arg::new("input-file")
                        .short('c')
                        .long("disassemble")
                        .value_name("FILE")
                        .about("Binary file to be disassembled")
                        .takes_value(true)
                        .required(true),
                ),
        )
        .subcommand(
            App::new("compile")
                .about("Compile source files to RISC-V ELF binaries")
                .arg(
                    Arg::new("input-file")
                        .about("Source file to be compiled")
                        .short('c')
                        .long("input-file")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("compiler")
                        .about("Compiler to be used")
                        .short('k')
                        .long("compiler")
                        .takes_value(true)
                        .value_name("COMPILER")
                        .possible_values(&["clang", "selfie"])
                        .default_value("selfie"),
                ),
        )
        .subcommand(
            App::new("cfg")
                .about("Generate control flow graph from RISC-U ELF binary")
                .arg(
                    Arg::new("input-file")
                        .about("Source RISC-U binary to be analyzed")
                        .short('c')
                        .long("input-file")
                        .takes_value(true)
                        .value_name("FILE")
                        .required(true),
                )
                .arg(
                    Arg::new("output-file")
                        .about("Output file to write to")
                        .short('o')
                        .long("output-file")
                        .takes_value(true)
                        .value_name("FILE")
                        .default_value("cfg.dot"),
                )
                .arg(
                    Arg::new("format")
                        .about("File format of the generated CFG")
                        .short('f')
                        .long("format")
                        .takes_value(true)
                        .possible_values(&["dot", "png"])
                        .default_value("dot"),
                ),
        )
        .subcommand(App::new("smt"))
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .global_setting(AppSettings::GlobalVersion)
}

mod common;

use bytesize::ByteSize;
use common::{compile_riscu, init};
use log::trace;
use monster::{self, rarity::*};
use rayon::prelude::*;
use std::{fs, process::Command};

#[test]
fn test_rarity_simulation() {
    init();

    compile_riscu(Some(&["three-level-nested-loop-1-35.c"]))
        .1
        .for_each(|(source, object)| {
            Command::new("rm")
                .arg("-f")
                .arg(
                    format!(
                        "{}/dumps",
                        std::env::current_dir()
                            .unwrap()
                            .canonicalize()
                            .unwrap()
                            .display()
                    )
                    .as_str(),
                )
                .output()
                .expect("can delte dump files");

            let output_dir = std::env::current_dir().unwrap().join("dumps");

            let result = execute(&object, &output_dir, ByteSize::mb(1), 1, 1);

            trace!("execution finished: {:?}", result);

            assert!(
                matches!(result, Ok(None)),
                "can rarity simulate '{}' without error ({:?})",
                source.to_str().unwrap(),
                result,
            );

            assert!(fs::metadata(output_dir.join("dump_0.out"))
                .unwrap()
                .is_file());
        });
}

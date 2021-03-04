use bytesize::ByteSize;
use log::trace;
use monster::{self, rarity::*};
use rayon::prelude::*;
use utils::{compile_riscu, init, with_temp_dir};

#[test]
fn test_rarity_simulation() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, Some(&["three-level-nested-loop-1-35.c"])).for_each(
            |(source, object)| {
                let result = execute(
                    &object,
                    ByteSize::mb(1),
                    1,
                    1,
                    1,
                    1,
                    0.6,
                    MetricType::Harmonic,
                );

                trace!("execution finished: {:?}", result);

                assert!(
                    matches!(result, Ok(None)),
                    "can rarity simulate '{}' without error ({:?})",
                    source.to_str().unwrap(),
                    result,
                );
            },
        );
    });
}

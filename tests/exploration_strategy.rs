mod common;

use common::{compile_all_riscu, convert_dot_to_png_and_check, init, time};
use monster::cfg::build_cfg_from_file;
use monster::exploration_strategy::*;
use petgraph::dot::Dot;
use rayon::prelude::*;
use std::{
    fs::{metadata, File},
    io::prelude::*,
};

#[test]
fn can_build_control_flow_graph_with_distance_from_exit() {
    init();

    compile_all_riscu().1
        .for_each(|(source_file, object_file)| {
        let ((graph, _), program) = time(format!("compute cfg: {:?}", source_file).as_str(), || {
            build_cfg_from_file(object_file.clone()).unwrap()
        });

        let strategy = ShortestPathStrategy::new(&graph, program.entry_address);

        let src_file_name = source_file.file_name().unwrap().to_str().unwrap();
        let dot_file = source_file
            .with_extension("dot")
            .with_file_name(src_file_name.replace(".c", "_distance.dot"));

        let mut f = File::create(dot_file.clone()).unwrap();
        f.write_fmt(format_args!("{:?}", strategy)).unwrap();

        assert!(
            dot_file.exists(),
            "can create CFG file with distances for: {:?}",
            source_file
        );
        assert!(
            metadata(dot_file.clone()).unwrap().len() > 0,
            "CFG file is not empty for: {:?}",
            source_file
        );

        let instructions_in_program = program.code_segment.len() / 4;
        let actually = strategy.distances().len() as f64 / instructions_in_program as f64;

        assert!(
            actually > 0.75,
            "at least 75% (actually: {:.1}%) of the instructions are reachable and have a distance assigned for: {:?}",
            actually * 100.0,
            source_file
            );

        if cfg!(feature = "pictures") {
            convert_dot_to_png_and_check(dot_file).unwrap();
        }
    });
}

#[test]
fn can_unroll_procedures_in_control_flow_graph() {
    init();

    compile_all_riscu()
        .1
        .for_each(|(source_file, object_file)| {
            let ((graph, _), program) =
                time(format!("compute cfg: {:?}", source_file).as_str(), || {
                    build_cfg_from_file(object_file.clone()).unwrap()
                });

            let strategy = ShortestPathStrategy::new(&graph, program.entry_address);

            let dot_file = source_file.with_extension("dot");

            let mut f = File::create(dot_file.clone()).unwrap();
            f.write_fmt(format_args!("{:?}", strategy)).unwrap();

            let unrolled = compute_unrolled_cfg(&graph);
            let dot_file = dot_file.with_file_name(
                dot_file
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .replace(".dot", "_unrolled.dot"),
            );

            let mut f = File::create(dot_file.clone()).unwrap();
            let dot_graph = Dot::with_config(&unrolled, &[]);
            write!(f, "{:?}", dot_graph).unwrap();

            assert!(
                dot_file.exists(),
                "can create unrolled CFG for: {:?}",
                source_file
            );
            assert!(
                metadata(dot_file.clone()).unwrap().len() > 0,
                "unrolled CFG file is not empty for: {:?}",
                source_file
            );

            if cfg!(feature = "pictures") {
                convert_dot_to_png_and_check(dot_file).unwrap();
            }
        });
}

use monster::path_exploration::*;
use petgraph::dot::Dot;
use rayon::prelude::*;
use riscu::load_object_file;
use std::{
    fs::{metadata, File},
    io::prelude::*,
};
use utils::{compile_riscu, convert_dot_to_png_and_check, init, time, with_temp_dir};

#[test]
fn can_build_control_flow_graph_with_distance_from_exit() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, None)
        .for_each(|(source_file, object_file)| {
        let program = load_object_file(object_file).unwrap();

        let strategy = time(format!("compute cfg: {:?}", source_file).as_str(), || {
            ShortestPathStrategy::compute_for(&program).unwrap()
        });

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

        let instructions_in_program = program.code.content.len() / 4;
        let actually = strategy.distances().len() as f64 / instructions_in_program as f64;

        if !source_file.ends_with("endless-loop.c") {
            assert!(
                actually > 0.75,
                "at least 75% (actually: {:.1}%) of the instructions are reachable and have a distance assigned for: {:?}",
                actually * 100.0,
                source_file
                );
        }

        if cfg!(feature = "pictures") {
            convert_dot_to_png_and_check(dot_file).unwrap();
        }
    });
    });
}

#[test]
fn can_unroll_procedures_in_control_flow_graph() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, None).for_each(|(source_file, object_file)| {
            let program = load_object_file(object_file).unwrap();
            let cfg = time(format!("compute cfg: {:?}", source_file).as_str(), || {
                ControlFlowGraph::build_for(&program).unwrap()
            });

            let strategy = ShortestPathStrategy::compute_for(&program);

            let dot_file = source_file.with_extension("dot");

            let mut f = File::create(dot_file.clone()).unwrap();
            f.write_fmt(format_args!("{:?}", strategy)).unwrap();

            let unrolled = compute_unrolled_cfg(&cfg);
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
    });
}

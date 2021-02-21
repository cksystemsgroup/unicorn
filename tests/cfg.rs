mod common;

use common::{compile_riscu, convert_dot_to_png_and_check, init, time, with_temp_dir};
use monster::path_exploration::*;
use petgraph::dot::Dot;
use rayon::prelude::*;
use std::{fs::File, io::prelude::*};

const GENERATE_CFG_PICTURES: bool = false;

#[test]
fn can_build_control_flow_graph() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, None).for_each(|(source, object)| {
            let program = riscu::load_object_file(object).unwrap();

            let cfg = time(format!("compute cfg: {:?}", source).as_str(), || {
                ControlFlowGraph::build_for(&program).unwrap()
            });

            let dot_graph = Dot::with_config(&cfg.graph, &[]);

            let dot_file = source.with_extension("dot");

            let mut f = File::create(dot_file.clone()).unwrap();
            f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

            if GENERATE_CFG_PICTURES {
                convert_dot_to_png_and_check(dot_file).unwrap();
            }
        });
    });
}

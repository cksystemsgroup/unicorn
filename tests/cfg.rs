mod common;

use common::{compile_riscu, convert_dot_to_png_and_check, init, time};
use monster::cfg::*;
use petgraph::dot::Dot;
use rayon::prelude::*;
use std::{fs::File, io::prelude::*};

#[test]
fn can_build_control_flow_graph() {
    init();

    compile_riscu(None).1.for_each(|(source, object)| {
        let ((graph, _), _) = time(format!("compute cfg: {:?}", source).as_str(), || {
            build_cfg_from_file(object.clone()).unwrap()
        });

        let dot_graph = Dot::with_config(&graph, &[]);

        let dot_file = source.with_extension("dot");

        let mut f = File::create(dot_file.clone()).unwrap();
        f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

        if cfg!(feature = "pictures") {
            convert_dot_to_png_and_check(dot_file).unwrap();
        }
    });
}

use monster::cfg::*;
use petgraph::dot::Dot;
use std::{fs::File, io::prelude::*};

mod common;

use common::time;

#[test]
fn can_build_control_flow_graph() {
    common::forall_compiled_riscu(move |path| {
        let (graph, _, _) = time(format!("compute cfg: {:?}", path), || {
            build_cfg_from_file(path.clone()).unwrap()
        });

        let dot_graph = Dot::with_config(&graph, &[]);

        let dot_file = path.with_extension("dot");

        let mut f = File::create(dot_file).unwrap();
        f.write_fmt(format_args!("{:?}", dot_graph)).unwrap();

        //let png_file = dot_file.with_extension("png");

        //let dfile = dot_file.as_path();
        //let pfile = png_file.as_path();

        //time(String::from("dot-to-png"), || {
        //  common::convert_dot_to_png(dfile, pfile).unwrap();
        //});
    });
}

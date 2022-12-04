use crate::guinea::graph::{evaluate_node, AllBeatorNodeTemplates, BeatorResponse};
use crate::guinea::graph_util::process_line;
use crate::guinea::Guineacorn;
use egui::Ui;
use egui_node_graph::NodeResponse;
use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::io::BufRead;
use std::path::PathBuf;
use std::str::FromStr;

pub fn input_window(data: &mut Guineacorn, ui: &mut Ui) {
    ui.horizontal_wrapped(|ui| {
        ui.label("Select a BTOR2 file to start.");
        if ui.button("Open file...").clicked() {
            data.reset_model_params();
            if let Some(path) = rfd::FileDialog::new().pick_file() {
                data.picked_path = Some(path.display().to_string());
            }
        }
    });

    let picked_path = data
        .picked_path
        .clone()
        .unwrap_or_else(|| "NONE".to_string());

    ui.add_space(10.0);
    ui.add_enabled_ui(data.picked_path.is_some(), |ui| {
        ui.label("Selected File:");
        ui.monospace(&picked_path);

        if ui.button("Load File").clicked() {
            data.reset_model_params();
            // TODO: do proper input validation
            let path = PathBuf::from_str(&picked_path).unwrap();
            let file = File::open(path).unwrap();
            let lines = io::BufReader::new(file).lines();
            lines
                .flatten()
                .filter(|x| !x.starts_with(';') && !x.is_empty())
                .for_each(|x| process_line(&mut data.node_graph, x));
        }
    });
    ui.label(format!["Output: {}", data.node_graph.out]);
}

pub fn output_window(data: &mut Guineacorn, ui: &mut Ui) {
    let graph_response = data.node_graph.state.draw_graph_editor(
        ui,
        AllBeatorNodeTemplates,
        &mut data.node_graph.user_state,
    );

    for node_response in graph_response.node_responses {
        if let NodeResponse::User(user_event) = node_response {
            match user_event {
                BeatorResponse::SetActiveNode(node) => {
                    data.node_graph.user_state.active_node = Some(node)
                }
                BeatorResponse::ClearActiveNode => data.node_graph.user_state.active_node = None,
            }
        }
    }

    if let Some(node) = data.node_graph.user_state.active_node {
        if data.node_graph.state.graph.nodes.contains_key(node) {
            let text = match evaluate_node(&data.node_graph.state.graph, node, &mut HashMap::new())
            {
                Ok(value) => format!("The result is: {:?}", value),
                Err(err) => format!("Execution error: {}", err),
            };
            data.node_graph.out = text;
        } else {
            data.node_graph.user_state.active_node = None;
        }
    }
}

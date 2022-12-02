use crate::guinea::graph::{evaluate_node, AllBeatorNodeTemplates, BeatorResponse};
use crate::guinea::Guineacorn;
use egui::Ui;
use egui_node_graph::NodeResponse;
use std::collections::HashMap;

pub fn input_window(data: &mut Guineacorn, ui: &mut Ui) {
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

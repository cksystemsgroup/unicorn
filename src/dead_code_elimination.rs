use crate::cfg::ControlFlowGraph;
use petgraph::graph::NodeIndex;
use petgraph::graph::Graph;

// given a root node and a graph we delete every single graph component not connected to the root node

// to keep track of the NodeIndex of the newly created node
struct NodeDuo {
    pub dead_index: NodeIndex,
    pub alive_index: NodeIndex,
}

fn node_added(added_nodes: Vec, node_index: NodeIndex) -> bool {
    for current_node in added_nodes {
        if current_node.dead_index == node_index {
            true
        }
    }
    false
}

pub fn eliminate_dead_code(graph_dead: &ControlFlowGraph, root: NodeIndex) -> ControlFlowGraph {
    let mut graph_alive = ControlFlowGraph::new();
    let mut added_nodes = Vec::new(); //to improve runtime add only nodes with 2 outgoing edges
    let mut node_stack = Vec::new(); //Nodes which neighbors haven't been added yet

    //add node to graph_alive and add NodeDuo to node_stack
    node_stack.push(NodeDuo::new(dead_index = root,
                                 alive_index = graph_alive.add_node(graph_dead.node_weight(root))));

    while let Some(current_node) = node_stack.pop() {
        for neighbor in graph_dead.neighbors_directed(current_node.dead_index, Incoming) {
            //if one of the neighbors has not been added yet we add it to our ControlFlowGraph
            if !node_added(added_nodes, neighbor) {
                
            }
        }
    }
}

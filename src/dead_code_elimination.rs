use crate::cfg::ControlFlowGraph;
use petgraph::graph::NodeIndex;
use petgraph::graph::Graph;

// given a root node and a graph we delete every single graph component not connected to the root node

// to keep track of the NodeIndex of the newly created node
struct NodeDuo {
    pub dead_index: NodeIndex,
    pub alive_index: NodeIndex,
}

fn node_added(added_nodes: Vec, node_index: NodeIndex) -> Result<NodeDuo, Error> {
    for x in 0..added_nodes.len() {
        if added_nodes[x].dead_index == node_index {
            added_nodes.remove(x)
        }
    }
    //TODO: Error handling
}

fn more_than_one_outgoing_edge(graph: &ControlFlowGraph, node: NodeIndex) -> bool {
    if graph.edges_directed(node, Outgoing).next() != None {
        true
    } else {
        false
    }
}

pub fn eliminate_dead_code(graph_dead: &ControlFlowGraph, root: NodeIndex) -> ControlFlowGraph {
    let mut graph_alive = ControlFlowGraph::new();
    let mut added_nodes = Vec::new(); //to improve runtime add only nodes with 2 outgoing edges
    let mut node_stack = Vec::new(); //Nodes which neighbors haven't been added yet

    //add node to graph_alive and add NodeDuo to node_stack
    node_stack.push(NodeDuo::new(dead_index = root,
                                 alive_index = graph_alive.add_node(graph_dead.node_weight(root))));

    //as long as stack isn't empty
    while let Some(current_node) = node_stack.pop() {
        for neighbor in graph_dead.neighbors_directed(current_node.dead_index, Incoming) {
            //if one of the neighbors has not been added yet we add it to our ControlFlowGraph
            let new_node_index = node_added(added_nodes, neighbor);
            if new_node_index != true  {
                let new_node_index = graph_alive.add_node(graph_dead.node_weight(neighbor));
                //push found node on the stack
                node_stack.push(NodeDuo::new(dead_index = neighbor, alive_index = new_node_index));
                //to add new edge the weight has to be looked up in the old graph
                graph_alive.add_edge(new_node_index, current_node.alive_index,
                                     graph_dead.edge_weight(graph_dead.find_edge(neighbor, current_node.dead_index)));

                //if there are 2 outgoing edges
                if more_than_one_outgoing_edge(graph_dead, neighbor) {
                    added_nodes.push(NodeDuo::new(dead_index = neighbor, alive_index = new_node_index));
                }

            } else {
                //if the node has been added we only need to add the edge
                graph_alive.add_edge(new_node_index, current_node.alive_index,
                                     graph_dead.edge_weight(graph_dead.find_edge(neighbor, current_node.dead_index)));

            }
        }
    }
    graph_alive
}

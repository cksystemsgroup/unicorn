use crate::formula_graph::Formula;
use petgraph::graph::NodeIndex;
use petgraph::Direction;

//to keep track of the NodeIndex of the newly created Node
struct NodeDuo {
    pub dead_index: NodeIndex,
    pub alive_index: NodeIndex,
}

//return the index of a NodeDuo in a Vec
fn get_node_index(added_nodes: &[NodeDuo], node_index: NodeIndex) -> Option<usize> {
    for (x, node) in added_nodes.iter().enumerate() {
        if node.dead_index == node_index {
            return Some(x);
        }
    }
    None
}

//check if Node has more than one outgoing Edge
fn more_than_one_outgoing_edge(graph: &Formula, node: NodeIndex) -> bool {
    graph.edges_directed(node, Direction::Outgoing).next() != None
}

#[allow(dead_code)]
//given a data-flow graph and a root Node we return a data-flow graph without any dead code
pub fn eliminate_dead_code(graph_dead: &Formula, root: NodeIndex) -> Formula {
    let mut graph_alive = Formula::new();
    let mut added_nodes: Vec<NodeDuo> = Vec::new(); //to improve runtime we only add Nodes with 2 outgoing Edges
    let mut node_stack: Vec<NodeDuo> = Vec::new(); //Nodes which neighbors haven't been added yet

    //add node to graph_alive and add the NodeDuo to node_stack
    node_stack.push(NodeDuo {
        dead_index: root,
        alive_index: graph_alive.add_node(graph_dead.node_weight(root).unwrap().to_owned()),
    });

    while let Some(current_node) = node_stack.pop() {
        //for every neighbor of a Node
        for neighbor in graph_dead.neighbors_directed(current_node.dead_index, Direction::Incoming)
        {
            //check if the neighbour has been added to our Graph
            let node_index = get_node_index(&added_nodes, neighbor);

            //if the Node has been added we only need to add the Edge
            //and remove the Node from added_nodes since there can only be 2 outgoing Edges
            //therefore the Node and all its Edges have been added and we won't need to check if
            //it's a duplicate ever again
            if let Some(index) = node_index {
                graph_alive.add_edge(
                    added_nodes.remove(index).alive_index,
                    current_node.alive_index,
                    graph_dead
                        .edge_weight(
                            graph_dead
                                .find_edge(neighbor, current_node.dead_index)
                                .unwrap()
                                .to_owned(),
                        )
                        .unwrap()
                        .to_owned(),
                );

            //if it hasn't been added yet
            } else {
                let new_node_index =
                    graph_alive.add_node(graph_dead.node_weight(neighbor).unwrap().to_owned());
                //push found Node on the stack
                node_stack.push(NodeDuo {
                    dead_index: neighbor,
                    alive_index: new_node_index,
                });
                //to add new Edge the weight has to be looked up in the old graph
                graph_alive.add_edge(
                    new_node_index,
                    current_node.alive_index,
                    graph_dead
                        .edge_weight(
                            graph_dead
                                .find_edge(neighbor, current_node.dead_index)
                                .unwrap()
                                .to_owned(),
                        )
                        .unwrap()
                        .to_owned(),
                );

                //if there are 2 outgoing Edges
                if more_than_one_outgoing_edge(&graph_dead, neighbor) {
                    added_nodes.push(NodeDuo {
                        dead_index: neighbor,
                        alive_index: new_node_index,
                    });
                }
            }
        }
    }
    graph_alive
}

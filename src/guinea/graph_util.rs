use crate::guinea::graph::ConcSymb::Concrete;
use crate::guinea::graph::{BeatorTemplate, BeatorValueType, NodeGraph, Sort};
use egui::Pos2;
use egui_node_graph::{InputId, NodeId, NodeTemplateTrait, OutputId};
use std::borrow::BorrowMut;
use std::cmp::max;
use std::collections::HashMap;

pub fn process_line(data: &mut NodeGraph, line: String) {
    let line_elements: Vec<&str> = line.split(' ').collect();
    match *line_elements.as_slice() {
        [nid, "sort", "bitvec", "1", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Boolean(false));
        }
        [nid, "sort", "bitvec", "64", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "sort", "array", "2", "2", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Array(HashMap::new()));
        }
        [nid, "sort", "bitvec", "8", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "sort", "bitvec", "16", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "sort", "bitvec", "24", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "sort", "bitvec", "32", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "sort", "bitvec", "40", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "sort", "bitvec", "48", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "sort", "bitvec", "56", ..] => {
            data.user_state
                .sort_map
                .insert(nid.parse().unwrap(), Sort::Bitvec(Concrete(0)));
        }
        [nid, "constd", sort, imm] => {
            process_const(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                imm.parse().unwrap(),
            );
        }
        [nid, "state", sort, name] => {
            process_state(data, nid.parse().unwrap(), sort.parse().unwrap(), name);
        }
        [nid, "uext", sort, parent, ..] => {
            process_ext(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                parent.parse().unwrap(),
            );
        }
        [nid, "eq", sort, left, right] => {
            process_eq(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "not", sort, parent] => {
            process_not(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                parent.parse().unwrap(),
            );
        }
        [nid, "bad", cond, name] => {
            process_bad(data, nid.parse().unwrap(), cond.parse().unwrap(), name);
        }
        [_, "init", _, state, init] => {
            process_init(data, state.parse().unwrap(), init.parse().unwrap());
        }
        [nid, "and", sort, left, right] => {
            process_and(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "add", sort, left, right] => {
            process_add(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "sub", sort, left, right] => {
            process_sub(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "mul", sort, left, right] => {
            process_mul(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "div", sort, left, right] => {
            process_div(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "urem", sort, left, right] => {
            process_rem(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "sll", sort, left, right] => {
            process_sll(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "srl", sort, left, right] => {
            process_srl(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "ult", sort, left, right] => {
            process_ult(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "ite", sort, cond, left, right] => {
            process_ite(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                cond.parse().unwrap(),
                left.parse().unwrap(),
                right.parse().unwrap(),
            );
        }
        [nid, "next", sort, state, next] => process_next(
            data,
            nid.parse().unwrap(),
            sort.parse().unwrap(),
            state.parse().unwrap(),
            next.parse().unwrap(),
        ),
        [nid, "input", sort, name] => {
            process_input(data, nid.parse().unwrap(), sort.parse().unwrap(), name)
        }
        [nid, "write", sort, memory, address, value] => {
            process_write(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                memory.parse().unwrap(),
                address.parse().unwrap(),
                value.parse().unwrap(),
            );
        }
        [nid, "read", sort, memory, address] => {
            process_read(
                data,
                nid.parse().unwrap(),
                sort.parse().unwrap(),
                memory.parse().unwrap(),
                address.parse().unwrap(),
            );
        }

        _ => println!("Can't process: {:?}", line_elements),
    };
}

fn process_const(data: &mut NodeGraph, nid: usize, sort: usize, imm: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let node = create_node(data, nid, BeatorTemplate::Const, 0, s.clone());

    if let Some(n) = get_inward(data, node, "Immediate") {
        data.state.graph[n].value = BeatorValueType::Sort {
            value: match s {
                Sort::Boolean(_) => Sort::Boolean(imm != 0),
                Sort::Bitvec(_) => Sort::Bitvec(Concrete(imm as u64)),
                _ => panic!("Cannot create const from: {:?}", s),
            },
        };
    };
}

fn process_read(data: &mut NodeGraph, nid: usize, sort: usize, memory: usize, address: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let mnode = *data.user_state.nid_map.get(&memory).unwrap();
    let anode = *data.user_state.nid_map.get(&address).unwrap();

    let x = max(get_x(data, mnode), get_x(data, anode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Read, x, s);

    let minward = get_inward(data, node, "Memory").unwrap();
    let moutward = get_outwart(data, mnode).unwrap();
    let ainward = get_inward(data, node, "Address").unwrap();
    let aoutward = get_outwart(data, anode).unwrap();

    link_nodes(data, moutward, minward);
    link_nodes(data, aoutward, ainward);
}

fn process_write(
    data: &mut NodeGraph,
    nid: usize,
    sort: usize,
    memory: usize,
    address: usize,
    value: usize,
) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let mnode = *data.user_state.nid_map.get(&memory).unwrap();
    let anode = *data.user_state.nid_map.get(&address).unwrap();
    let vnode = *data.user_state.nid_map.get(&value).unwrap();

    let x = max(get_x(data, anode), get_x(data, vnode));
    let x = max(get_x(data, mnode), x) + 1;
    let node = create_node(data, nid, BeatorTemplate::Write, x, s);

    let minward = get_inward(data, node, "Memory").unwrap();
    let moutward = get_outwart(data, mnode).unwrap();
    let ainward = get_inward(data, node, "Address").unwrap();
    let aoutward = get_outwart(data, anode).unwrap();
    let vinward = get_inward(data, node, "Value").unwrap();
    let voutward = get_outwart(data, vnode).unwrap();

    link_nodes(data, moutward, minward);
    link_nodes(data, aoutward, ainward);
    link_nodes(data, voutward, vinward);
}

fn process_add(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Add, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_sub(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Sub, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_mul(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Mul, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_div(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Div, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_rem(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Rem, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_sll(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Sll, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_srl(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Srl, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_ult(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Ult, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_ext(data: &mut NodeGraph, nid: usize, sort: usize, parent: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let pnode = *data.user_state.nid_map.get(&parent).unwrap();

    let node = create_node(data, nid, BeatorTemplate::Ext, get_x(data, pnode) + 1, s);
    let inward = get_inward(data, node, "From").unwrap();
    let outward = get_outwart(data, pnode).unwrap();

    link_nodes(data, outward, inward);
}

fn process_ite(
    data: &mut NodeGraph,
    nid: usize,
    sort: usize,
    cond: usize,
    left: usize,
    right: usize,
) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let cnode = *data.user_state.nid_map.get(&cond).unwrap();
    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode));
    let x = max(get_x(data, cnode), x) + 1;
    let node = create_node(data, nid, BeatorTemplate::Ite, x, s);

    let cinward = get_inward(data, node, "Condition").unwrap();
    let coutward = get_outwart(data, cnode).unwrap();
    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, coutward, cinward);
    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_eq(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Eq, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_and(data: &mut NodeGraph, nid: usize, sort: usize, left: usize, right: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let lnode = *data.user_state.nid_map.get(&left).unwrap();
    let rnode = *data.user_state.nid_map.get(&right).unwrap();

    let x = max(get_x(data, lnode), get_x(data, rnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::And, x, s);

    let linward = get_inward(data, node, "Left").unwrap();
    let loutward = get_outwart(data, lnode).unwrap();
    let rinward = get_inward(data, node, "Right").unwrap();
    let routward = get_outwart(data, rnode).unwrap();

    link_nodes(data, loutward, linward);
    link_nodes(data, routward, rinward);
}

fn process_not(data: &mut NodeGraph, nid: usize, sort: usize, parent: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let pnode = *data.user_state.nid_map.get(&parent).unwrap();

    let node = create_node(data, nid, BeatorTemplate::Not, get_x(data, pnode) + 1, s);
    let inward = get_inward(data, node, "Value").unwrap();
    let outward = get_outwart(data, pnode).unwrap();

    link_nodes(data, outward, inward);
}

fn process_state(data: &mut NodeGraph, nid: usize, sort: usize, name: &str) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let node = create_node(data, nid, BeatorTemplate::State, 0, s);

    if let Some(n) = get_inward(data, node, "Name") {
        data.state.graph[n].value = BeatorValueType::Sort {
            value: Sort::String(name.to_string()),
        }
    };
}

fn process_init(data: &mut NodeGraph, state: usize, initial: usize) {
    let state = *data.user_state.nid_map.get(&state).unwrap();
    let init = *data.user_state.nid_map.get(&initial).unwrap();

    let inward = get_inward(data, state, "Initial Value").unwrap();
    let outward = get_outwart(data, init).unwrap();
    link_nodes(data, outward, inward);

    let init_x = data.state.node_positions.get(init).unwrap().x;
    let x = init_x as usize + 1;
    let y = data.lookup_y_and_inc(x);

    data.state
        .node_positions
        .insert(state, Pos2::new(x as f32 * 150.0, y as f32 * 200.0));

    data.state.graph.nodes.get_mut(state).unwrap().user_data.x = x;
}

fn process_next(data: &mut NodeGraph, nid: usize, sort: usize, state: usize, new_value: usize) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let snode = *data.user_state.nid_map.get(&state).unwrap();
    let nnode = *data.user_state.nid_map.get(&new_value).unwrap();

    let x = max(get_x(data, snode), get_x(data, nnode)) + 1;
    let node = create_node(data, nid, BeatorTemplate::Next, x, s);

    let sinward = get_inward(data, node, "State").unwrap();
    let soutward = get_outwart(data, snode).unwrap();
    let ninward = get_inward(data, node, "Next").unwrap();
    let noutward = get_outwart(data, nnode).unwrap();

    link_nodes(data, soutward, sinward);
    link_nodes(data, noutward, ninward);
}

fn process_input(data: &mut NodeGraph, nid: usize, sort: usize, name: &str) {
    let s = data.user_state.sort_map.get(&sort).unwrap().clone();

    let node = create_node(data, nid, BeatorTemplate::State, 0, s);

    if let Some(n) = get_inward(data, node, "Name") {
        data.state.graph[n].value = BeatorValueType::Sort {
            value: Sort::String(name.to_string()),
        }
    };
}

fn process_bad(data: &mut NodeGraph, nid: usize, cond: usize, name: &str) {
    let pnode = *data.user_state.nid_map.get(&cond).unwrap();

    let node = create_node(
        data,
        nid,
        BeatorTemplate::Bad,
        get_x(data, pnode) + 1,
        Sort::Error,
    );
    let inward = get_inward(data, node, "Condition").unwrap();
    let outward = get_outwart(data, pnode).unwrap();

    link_nodes(data, outward, inward);

    if let Some(n) = get_inward(data, node, "Name") {
        data.state.graph[n].value = BeatorValueType::Sort {
            value: Sort::String(name.to_string()),
        }
    };
}

pub fn create_node(
    data: &mut NodeGraph,
    nid: usize,
    kind: BeatorTemplate,
    x: usize,
    sort: Sort,
) -> NodeId {
    let user_state = data.user_state.borrow_mut();
    let new_node = data.state.graph.add_node(
        kind.node_graph_label(user_state),
        kind.user_data(user_state),
        |graph, node_id| kind.build_node(graph, user_state, node_id),
    );

    let y = data.lookup_y_and_inc(x);

    data.state
        .graph
        .nodes
        .get_mut(new_node)
        .unwrap()
        .user_data
        .sort = sort;

    data.state
        .graph
        .nodes
        .get_mut(new_node)
        .unwrap()
        .user_data
        .x = x;

    data.state
        .node_positions
        .insert(new_node, Pos2::new(x as f32 * 150.0, y as f32 * 200.0));
    data.state.node_order.push(new_node);

    data.user_state.nid_map.insert(nid, new_node);

    new_node
}

fn link_nodes(data: &mut NodeGraph, outward: OutputId, inward: InputId) {
    data.state.graph.add_connection(outward, inward);
}

fn get_inward(data: &NodeGraph, node: NodeId, name: &str) -> Option<InputId> {
    data.state.graph.nodes.get(node)?.get_input(name).ok()
}

fn get_outwart(data: &NodeGraph, node: NodeId) -> Option<OutputId> {
    data.state.graph.nodes.get(node)?.get_output("Output").ok()
}

fn get_x(data: &NodeGraph, node: NodeId) -> usize {
    data.state.graph.nodes.get(node).unwrap().user_data.x
}

use std::collections::HashMap;

use egui::{Color32, Pos2, Rect, Rounding, Stroke, Ui, Vec2};

use crate::guinea::giraphe::draw::SugiNode::{Dummy, Real};
use crate::guinea::giraphe::Giraphe;
use crate::unicorn::Nid;

// struct was edge ist mit in und out edge
// layout struct um das layout zu speichern und bei dem impl draw um das zu zeichnen
#[derive(Eq, PartialEq, Hash, Debug, Copy, Clone)]
enum SugiNode {
    Real(Nid),
    Dummy(Nid),
}

#[derive(Default, Debug)]
pub struct Layout {
    parent_to_children: HashMap<SugiNode, Vec<SugiNode>>,
    _child_to_parents: HashMap<SugiNode, Vec<SugiNode>>,
    node_to_layer: HashMap<SugiNode, isize>,
    layer_to_node: HashMap<isize, Vec<SugiNode>>,
}

impl Giraphe {
    fn layer_rec(&self, x: Nid, layers: &mut HashMap<SugiNode, isize>) {
        for p in self.spot_parents(x) {
            let layer_p = layers.get(&Real(p)).unwrap_or(&-1);
            let layer_x = layers.get(&Real(x)).unwrap_or(&-1);
            if layer_p < &(layer_x + 1) {
                layers.insert(Real(p), layer_x + 1);
                self.layer_rec(p, layers);
            }
        }
    }

    fn layer(&self) -> Layout {
        let mut node_to_layer = HashMap::new();
        let mut parent_to_children = HashMap::new();
        let mut child_to_parents = HashMap::new();

        // layers for real nodes
        for n in &self.roots {
            node_to_layer.insert(Real(*n), 0);
            self.layer_rec(*n, &mut node_to_layer);
        }

        // dummy nodes and edges
        let mut dummy_id = 0;
        for nid in self.spot_lookup.keys() {
            let node_layer = *node_to_layer.get(&Real(*nid)).expect("Has to be mapped");
            for child_nid in self.spot_parents(*nid) {
                let child_layer = *node_to_layer
                    .get(&Real(child_nid))
                    .expect("Has to be mapped");
                let mut n = Real(*nid);
                let mut i = 1;
                while i < child_layer - node_layer {
                    let entry_ptc = parent_to_children.entry(n).or_insert_with(Vec::new);
                    let dummy = Dummy(dummy_id);
                    let entry_ctp = child_to_parents.entry(dummy).or_insert_with(Vec::new);

                    entry_ptc.push(dummy);
                    entry_ctp.push(n);
                    node_to_layer.insert(dummy, node_layer + i);
                    n = dummy;
                    dummy_id += 1;
                    i += 1;
                }
                let entry_ptc = parent_to_children.entry(n).or_insert_with(Vec::new);
                let c = Real(child_nid);
                let entry_ctp = child_to_parents.entry(c).or_insert_with(Vec::new);
                entry_ptc.push(c);
                entry_ctp.push(n);
            }
        }

        // transform hashmap into vec/hashmap with inverted key values
        let mut layer_to_node = HashMap::new();
        for (k, v) in &node_to_layer {
            layer_to_node.entry(*v).or_insert_with(Vec::new).push(*k);
        }

        Layout {
            layer_to_node,
            parent_to_children,
            _child_to_parents: child_to_parents,
            node_to_layer,
        }
    }

    // TODO: reduce eye sore
    fn minimize_crossings(&self, layout: Layout) -> Layout {
        // // up
        // let mut layer_to_node_ordered_up = HashMap::new();
        // let mut layers: Vec<_> = layout.layer_to_node.iter().collect();
        // layers.sort_by(|(x, _), (y, _)| x.cmp(y));
        // let mut layer_iter = layers.into_iter();
        //
        // let (zero, roots) = layer_iter.next().unwrap();
        // layer_to_node_ordered_up.insert(*zero, roots.clone());
        // for (k, v) in layer_iter {
        //     let med = |x: &SugiNode| {
        //         let layer = layout.node_to_layer.get(x).expect("Must be mapped");
        //         let layer = layout
        //             .layer_to_node
        //             .get(&(layer - 1))
        //             .expect("Must be mapped");
        //         let pos: Vec<_> = layout
        //             .child_to_parents
        //             .get(x)
        //             .expect("Must be mapped")
        //             .iter()
        //             .map(|x| layer.iter().position(|y| y == x).unwrap())
        //             .collect();
        //         let mid = pos.len() / 2;
        //         if pos.len() == 0 {
        //             0.0
        //         } else if pos.len() % 2 == 0 {
        //             (pos[mid - 1] + pos[mid]) as f32 / 2.0
        //         } else {
        //             pos[mid] as f32
        //         }
        //     };
        //     let mut layer: Vec<_> = v.iter().map(|x| (x, med(x))).collect();
        //     layer.sort_by(|(_, a), (_, b)| a.total_cmp(b));
        //     let layer: Vec<_> = layer.iter().map(|x| *x.0).collect();
        //     layer_to_node_ordered_up.insert(*k, layer);
        // }
        // layout.layer_to_node = layer_to_node_ordered_up;
        //
        // // down
        // let mut layer_to_node_ordered_down = HashMap::new();
        // let mut layers: Vec<_> = layout.layer_to_node.iter().collect();
        // layers.sort_by(|(x, _), (y, _)| y.cmp(x));
        // let mut layer_iter = layers.into_iter();
        //
        // let (zero, roots) = layer_iter.next().unwrap();
        // layer_to_node_ordered_down.insert(*zero, roots.clone());
        // for (k, v) in layer_iter {
        //     let med = |x: &SugiNode| {
        //         let layer = layout.node_to_layer.get(x).expect("Must be mapped");
        //         let layer = layout
        //             .layer_to_node
        //             .get(&(layer + 1))
        //             .expect("Must be mapped");
        //         let pos = layout.parent_to_children.get(x);
        //         if let Some(pos) = pos {
        //             let pos: Vec<_> = pos
        //                 .iter()
        //                 .map(|x| layer.iter().position(|y| y == x).unwrap())
        //                 .collect();
        //             let mid = pos.len() / 2;
        //             if pos.len() % 2 == 0 {
        //                 (pos[mid - 1] + pos[mid]) as f32 / 2.0
        //             } else {
        //                 pos[mid] as f32
        //             }
        //         } else {
        //             0.0
        //         }
        //     };
        //     let mut layer: Vec<_> = v.iter().map(|x| (x, med(x))).collect();
        //     layer.sort_by(|(_, a), (_, b)| a.total_cmp(b));
        //     let layer: Vec<_> = layer.iter().map(|x| *x.0).collect();
        //     layer_to_node_ordered_down.insert(*k, layer);
        // }
        // layout.layer_to_node = layer_to_node_ordered_down;

        // median sorting with another hashmap for the x position
        layout
    }

    // layer with min amount of layers https://youtu.be/pKs53CuAo-8?t=82 oder das mit nr of roots: https://youtu.be/pKs53CuAo-8?t=408
    // minimize crossings: https://www.youtube.com/watch?v=K377XgzNkEA median/bary und dann greedy switch
    // layout 🥵: https://youtu.be/9B3ZXsRbiCw?t=228
    pub fn sugiyamer(&mut self) {
        let layout = self.layer();
        let layout = self.minimize_crossings(layout);
        self.layout = layout;
    }

    pub fn draw(&mut self, ui: &mut Ui) {
        let top_left = ui.min_rect().min.to_vec2() + Vec2::from([100.0, 100.0]) + self.pan;
        // TODO: proper positioning

        // draw edges
        for (parent, children) in &self.layout.parent_to_children {
            for child in children {
                let pos = |x| {
                    let layer = self.layout.node_to_layer.get(x).unwrap();
                    let x_pos = self
                        .layout
                        .layer_to_node
                        .get(layer)
                        .unwrap()
                        .iter()
                        .position(|y| y == x)
                        .unwrap();
                    Pos2::from([x_pos as f32 * 40.0, *layer as f32 * 40.0])
                };
                let parent_pos = pos(parent) + top_left;
                let child_pos = pos(child) + top_left;
                if ui.min_rect().contains(parent_pos) || ui.min_rect().contains(child_pos) {
                    ui.painter().line_segment(
                        [parent_pos, child_pos],
                        Stroke::from((5.0, Color32::from_gray(255))),
                    );
                }
            }
        }

        // draw nodes
        let mut layers: Vec<_> = self.layout.layer_to_node.iter().collect();
        layers.sort_by(|(x, _), (y, _)| x.cmp(y));
        for (y, nodes) in layers {
            for (x, n) in nodes.iter().enumerate() {
                if let Real(_) = n {
                    let rect = Rect::from_center_size(
                        Pos2::from([x as f32 * 40.0, *y as f32 * 40.0]) + top_left,
                        Vec2::from([20.0, 20.0]),
                    );
                    if ui.min_rect().intersects(rect) {
                        ui.painter().rect_filled(
                            rect,
                            Rounding::from(10.0),
                            Color32::from_gray(40),
                        );
                    }
                }
            }
        }
    }
}

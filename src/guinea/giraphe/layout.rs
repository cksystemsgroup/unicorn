use std::cmp::Ordering;
use std::iter::zip;

use indexmap::IndexMap;

use crate::guinea::giraphe::LayoutNode::{Dummy, Real};
use crate::guinea::giraphe::{Giraphe, Layout, LayoutNode, Pos};

impl Giraphe {
    fn layer(&self) -> Layout {
        let mut layers: Vec<Vec<_>> = vec![];
        let mut node_to_layer = IndexMap::<LayoutNode, isize>::new();
        let mut child_edges = IndexMap::<LayoutNode, Vec<LayoutNode>>::new();
        let mut edges_to_its_dummies = IndexMap::<(LayoutNode, LayoutNode), Vec<LayoutNode>>::new();

        // insert dummy nodes
        let mut dummy_idx = 0;
        for nid in self.node_lookup.keys().rev() {
            for children in self.node_to_children.get(nid).unwrap() {
                let edge = child_edges.entry(Real(*children)).or_insert_with(Vec::new);
                edge.push(Real(*nid));
            }
            let edges = child_edges.get(&Real(*nid));
            let layer = if let Some(edges) = edges {
                edges
                    .iter()
                    .map(|x| node_to_layer.get(x).unwrap_or(&-1))
                    .max()
                    .unwrap_or(&-1)
                    + 1
            } else {
                0
            };

            let more_than_one_layer_difference: Vec<_> =
                if let Some(edges) = child_edges.get(&Real(*nid)) {
                    edges
                        .iter()
                        .filter(|x| layer - 1 != *node_to_layer.get(*x).unwrap())
                        .cloned()
                        .collect()
                } else {
                    vec![]
                };

            for p in &more_than_one_layer_difference {
                let intermediate_dummies = edges_to_its_dummies
                    .entry((Real(*nid), *p))
                    .or_insert_with(Vec::new);
                let p_layer = *node_to_layer.get(p).unwrap();
                let mut i = 1;
                let mut n = *p;
                while i < layer - p_layer {
                    let d = Dummy(dummy_idx);
                    intermediate_dummies.push(d);
                    let e = child_edges.entry(d).or_insert_with(Vec::new);
                    node_to_layer.insert(d, p_layer + i);
                    layers[(p_layer + i) as usize].push(d);
                    e.push(n);
                    n = d;
                    dummy_idx += 1;
                    i += 1;
                }
                let e = child_edges.entry(Real(*nid)).or_insert_with(Vec::new);
                e.push(n);
            }

            if let Some(edges) = child_edges.get(&Real(*nid)) {
                let new_edges: Vec<_> = edges
                    .iter()
                    .filter(|item| !more_than_one_layer_difference.contains(item))
                    .copied()
                    .collect();
                child_edges.insert(Real(*nid), new_edges);
            }

            node_to_layer.insert(Real(*nid), layer);
            if layers.len() <= layer as usize {
                layers.push(vec![Real(*nid)]);
            } else {
                layers[layer as usize].push(Real(*nid));
            }
        }

        Layout {
            layers,
            child_edges,
            positions: IndexMap::new(),
            edges_to_its_dummies,
        }
    }

    fn minimize_crossings(&self, mut layout: Layout) -> Layout {
        let mut node_positions = IndexMap::<LayoutNode, Pos>::new();
        let mut used_positions = IndexMap::<Pos, Vec<LayoutNode>>::new();

        for (i, node) in layout.layers[0].iter().enumerate() {
            node_positions.insert(*node, Pos::new(i as f32, 0.0));
        }

        for (i, layer) in layout.layers.iter().enumerate().skip(1) {
            for n in layer {
                let edges: Option<&Vec<LayoutNode>> = layout.child_edges.get(n);
                let med_n = if let Some(edges) = edges {
                    fn get_y(z: &LayoutNode, pos_map: &IndexMap<LayoutNode, Pos>) -> f32 {
                        pos_map.get(z).unwrap().x
                    }
                    let mut vals = Vec::new();
                    for e in edges {
                        vals.push(get_y(e, &node_positions));
                    }
                    median(vals.as_slice()).unwrap_or(0.0)
                } else {
                    unreachable!("Only roots should have no children");
                };

                node_positions.insert(*n, Pos::new(med_n, i as f32));
                let overlaps = used_positions
                    .entry(Pos::new(med_n, i as f32))
                    .or_insert_with(Vec::new);
                overlaps.push(*n);
            }
        }

        // post process node positions (remove overlaps)
        for (k, v) in used_positions {
            let nr_of_overlaps = v.len();
            if nr_of_overlaps == 1 {
                continue;
            }

            let x: f32 = k.x - 0.4;
            for (n, i) in zip(v, 0..nr_of_overlaps) {
                node_positions.insert(
                    n,
                    Pos::new(x + (i as f32) / ((nr_of_overlaps - 1) as f32) * 0.8, k.y),
                );
            }
        }

        layout.positions = node_positions;

        layout
    }

    pub fn sugiyama(&mut self) {
        let layout = self.layer();
        let layout = self.minimize_crossings(layout);
        self.layout = layout;
    }
}

// from: https://rust-lang-nursery.github.io/rust-cookbook/science/mathematics/statistics.html
fn partition(data: &[f32]) -> Option<(Vec<f32>, f32, Vec<f32>)> {
    match data.len() {
        0 => None,
        _ => {
            let (pivot_slice, tail) = data.split_at(1);
            let pivot = pivot_slice[0];
            let (left, right) = tail.iter().fold((vec![], vec![]), |mut splits, next| {
                {
                    let (ref mut left, ref mut right) = &mut splits;
                    if next < &pivot {
                        left.push(*next);
                    } else {
                        right.push(*next);
                    }
                }
                splits
            });

            Some((left, pivot, right))
        }
    }
}

fn select(data: &[f32], k: usize) -> Option<f32> {
    let part = partition(data);

    match part {
        None => None,
        Some((left, pivot, right)) => {
            let pivot_idx = left.len();

            match pivot_idx.cmp(&k) {
                Ordering::Equal => Some(pivot),
                Ordering::Greater => select(&left, k),
                Ordering::Less => select(&right, k - (pivot_idx + 1)),
            }
        }
    }
}

fn median(data: &[f32]) -> Option<f32> {
    let size = data.len();

    match size {
        even if even % 2 == 0 => {
            let fst_med = select(data, (even / 2) - 1);
            let snd_med = select(data, even / 2);

            match (fst_med, snd_med) {
                (Some(fst), Some(snd)) => Some((fst + snd) / 2.0),
                _ => None,
            }
        }
        odd => select(data, odd / 2),
    }
}

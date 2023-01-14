use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::iter::zip;

use egui::{Color32, Pos2, Rect, Rounding, Stroke, Ui, Vec2};
use indexmap::IndexMap;

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

#[derive(Debug)]
struct Pos {
    x: f32,
    y: f32,
}

impl PartialEq for Pos {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl Eq for Pos {}

impl Pos {
    fn key(&self) -> u64 {
        ((self.x.to_bits() as u64) << 32) + self.y.to_bits() as u64
    }

    fn new(x: f32, y: f32) -> Self {
        Self { x, y }
    }
}

impl Hash for Pos {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state)
    }
}

#[derive(Default, Debug)]
pub struct Layout {
    layers: Vec<Vec<SugiNode>>,
    child_edges: IndexMap<SugiNode, Vec<SugiNode>>,
    positions: IndexMap<SugiNode, Pos>,
}

static X_SPACING: f32 = 50.0;
static Y_SPACING: f32 = 100.0;
impl Giraphe {
    fn layer(&self) -> Layout {
        let mut layers: Vec<Vec<_>> = vec![];
        let mut node_to_layer = IndexMap::<SugiNode, isize>::new();
        let mut child_edges = IndexMap::<SugiNode, Vec<SugiNode>>::new();

        let mut dummy_idx = 0;
        for k in self.spot_lookup.keys().rev() {
            for c in self.spot_parents(*k) {
                let e = child_edges.entry(Real(c)).or_insert_with(Vec::new);
                e.push(Real(*k));
            }
            let edges = child_edges.get(&Real(*k));
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
                if let Some(edges) = child_edges.get(&Real(*k)) {
                    edges
                        .iter()
                        .filter(|x| layer - 1 != *node_to_layer.get(*x).unwrap())
                        .cloned()
                        .collect()
                } else {
                    vec![]
                };

            // TODO: somewhere here populate parent_edges
            for p in &more_than_one_layer_difference {
                let p_layer = *node_to_layer.get(p).unwrap();
                let mut i = 1;
                let mut n = *p;
                while i < layer - p_layer {
                    let d = Dummy(dummy_idx);
                    let e = child_edges.entry(d).or_insert_with(Vec::new);
                    node_to_layer.insert(d, p_layer + i);
                    layers[(p_layer + i) as usize].push(d);
                    e.push(n);
                    n = d;
                    dummy_idx += 1;
                    i += 1;
                }
                let e = child_edges.entry(Real(*k)).or_insert_with(Vec::new);
                e.push(n);
            }

            if let Some(edges) = child_edges.get(&Real(*k)) {
                let new_edges: Vec<_> = edges
                    .iter()
                    .filter(|item| !more_than_one_layer_difference.contains(item))
                    .copied()
                    .collect();
                child_edges.insert(Real(*k), new_edges);
            }

            node_to_layer.insert(Real(*k), layer);
            if layers.len() <= layer as usize {
                layers.push(vec![Real(*k)]);
            } else {
                layers[layer as usize].push(Real(*k));
            }
        }

        Layout {
            layers,
            child_edges,
            positions: IndexMap::new(),
        }
    }

    fn minimize_crossings(&self, mut layout: Layout) -> Layout {
        // TODO: median ordering

        let mut node_positions = IndexMap::<SugiNode, Pos>::new();
        let mut used_positions = IndexMap::<Pos, Vec<SugiNode>>::new();

        for (i, node) in layout.layers[0].iter().enumerate() {
            node_positions.insert(*node, Pos::new(i as f32, 0.0));
        }

        for (i, layer) in layout.layers.iter().enumerate().skip(1) {
            for n in layer {
                let edges: Option<&Vec<SugiNode>> = layout.child_edges.get(n);
                let med_n = if let Some(edges) = edges {
                    fn get_y(z: &SugiNode, pos_map: &IndexMap<SugiNode, Pos>) -> f32 {
                        pos_map.get(z).unwrap().x
                    }
                    let mut vals = Vec::new();
                    for e in edges {
                        vals.push(get_y(e, &node_positions));
                    }
                    // TODO: avoid overlap
                    // TODO: also one down movement
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

            let x: f32 = k.x - 0.5;
            for (n, i) in zip(v, 0..nr_of_overlaps) {
                node_positions.insert(
                    n,
                    Pos::new(x + (i as f32) / ((nr_of_overlaps - 1) as f32), k.y),
                );
            }
        }

        layout.positions = node_positions;

        layout
    }

    pub fn sugiyamer(&mut self) {
        let layout = self.layer();
        let layout = self.minimize_crossings(layout);
        self.layout = layout;
    }

    pub fn draw(&mut self, ui: &mut Ui) {
        let top_left = ui.min_rect().min.to_vec2() + Vec2::from([100.0, 100.0]) + self.pan;

        // draw edges
        for (node, pos) in &self.layout.positions {
            let edges: Option<&Vec<SugiNode>> = self.layout.child_edges.get(node);
            if let Some(edges) = edges {
                for c_pos in edges.iter().map(|x| self.layout.positions.get(x).unwrap()) {
                    let parent_pos = Pos2::from((pos.x * X_SPACING, pos.y * Y_SPACING)) + top_left;
                    let child_pos =
                        Pos2::from((c_pos.x * X_SPACING, c_pos.y * Y_SPACING)) + top_left;
                    if ui.min_rect().contains(parent_pos) || ui.min_rect().contains(child_pos) {
                        ui.painter().line_segment(
                            [parent_pos, child_pos],
                            Stroke::from((5.0, Color32::from_gray(255))),
                        );
                    }
                }
            }
        }

        // draw nodes
        for (node, pos) in &self.layout.positions {
            if pos.y * Y_SPACING > ui.min_rect().bottom() {
                break;
            }

            if let Real(_) = node {
                let pos_x = pos.x * X_SPACING + top_left.x;
                if pos_x < ui.min_rect().left() || pos_x > ui.min_rect().right() {
                    continue;
                }
                let rect = Rect::from_center_size(
                    Pos2::from([pos.x * X_SPACING, pos.y * Y_SPACING]) + top_left,
                    Vec2::from([20.0, 20.0]),
                );

                ui.painter()
                    .rect_filled(rect, Rounding::from(10.0), Color32::from_gray(100));
            }
        }
    }
}

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

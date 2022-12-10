use crate::guinea::giraphe::{Giraphe, Spot};
use crate::unicorn::{Model, Node, NodeRef};
use egui::{Align, Color32, Layout, Rect, Rounding, Ui, Vec2};
use log::trace;
use std::cmp::max;
use std::collections::HashMap;

static XSIZE: f32 = 150.0;
static YSIZE: f32 = 200.0;
static NODE_MARGIN: f32 = 10.0;
static NODE_PADDING: f32 = 5.0;

impl Giraphe {
    pub fn from(model: &Model) -> Self {
        assert!(
            !model.lines.is_empty(),
            "Can't convert model before it was renumbered!"
        );

        let mut spot_lookup = HashMap::new();
        let mut spot_list = Vec::new();
        let mut leaves = Vec::new();

        let mut layers: Vec<u64> = Vec::new();
        let mut lookup_y = |x| {
            if let Some(y) = layers.get(x) {
                let ret = *y;
                *layers.get_mut(x).unwrap() += 1;
                ret
            } else {
                layers.push(1);
                0
            }
        };
        let lookup_nid = |n: &NodeRef| match &*n.borrow() {
            Node::Const { nid, .. }
            | Node::Read { nid, .. }
            | Node::Write { nid, .. }
            | Node::Add { nid, .. }
            | Node::Sub { nid, .. }
            | Node::Mul { nid, .. }
            | Node::Div { nid, .. }
            | Node::Rem { nid, .. }
            | Node::Sll { nid, .. }
            | Node::Srl { nid, .. }
            | Node::Ult { nid, .. }
            | Node::Ext { nid, .. }
            | Node::Ite { nid, .. }
            | Node::Eq { nid, .. }
            | Node::And { nid, .. }
            | Node::Not { nid, .. }
            | Node::State { nid, .. }
            | Node::Next { nid, .. }
            | Node::Input { nid, .. }
            | Node::Bad { nid, .. } => *nid,
            Node::Comment(_) => unreachable!(),
        };

        for node in &model.lines {
            let n = &*node.borrow();
            let spot = match n {
                Node::Comment(c) => {
                    trace!("Skipping comment in model2graph conversion: {c}");
                    continue;
                }
                _ => Spot::from(node),
            };

            match &*node.borrow() {
                // zero parents
                Node::Const { nid, .. } | Node::Input { nid, .. } => {
                    let s = &mut *spot.borrow_mut();
                    s.set_position(0.0, lookup_y(0) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid as u64, spot.clone());
                }

                // one parent
                Node::Not { nid, value, .. } | Node::Ext { nid, value, .. } => {
                    let px = spot_lookup.get(&lookup_nid(value)).unwrap();
                    let px = px.borrow().position.x;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(
                        px + XSIZE,
                        lookup_y(((px + XSIZE) / XSIZE) as usize) as f32 * YSIZE,
                    );

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid as u64, spot.clone());
                }
                // two parents
                Node::Read {
                    nid,
                    memory: left,
                    address: right,
                }
                | Node::Add { nid, left, right }
                | Node::Sub { nid, left, right }
                | Node::Mul { nid, left, right }
                | Node::Div { nid, left, right }
                | Node::Rem { nid, left, right }
                | Node::Sll { nid, left, right }
                | Node::Srl { nid, left, right }
                | Node::Ult { nid, left, right }
                | Node::Eq { nid, left, right }
                | Node::And {
                    nid, left, right, ..
                } => {
                    let lx = spot_lookup.get(&lookup_nid(left)).unwrap();
                    let lx = lx.borrow().position.x;
                    let rx = spot_lookup.get(&lookup_nid(right)).unwrap();
                    let rx = rx.borrow().position.x;
                    let x: u64 = (max(lx as u64, rx as u64) / XSIZE as u64) + 1;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid as u64, spot.clone());
                }
                // three parents
                Node::Ite {
                    nid,
                    cond: one,
                    left: two,
                    right: three,
                    ..
                }
                | Node::Write {
                    nid,
                    memory: one,
                    address: two,
                    value: three,
                } => {
                    let lx = spot_lookup.get(&lookup_nid(one)).unwrap();
                    let lx = lx.borrow().position.x;
                    let rx = spot_lookup.get(&lookup_nid(two)).unwrap();
                    let rx = rx.borrow().position.x;
                    let cx = spot_lookup.get(&lookup_nid(three)).unwrap();
                    let cx = cx.borrow().position.x;
                    let x = max(lx as u64, rx as u64);
                    let x: u64 = (max(x, cx as u64) / XSIZE as u64) + 1;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                }
                // special cases
                Node::State { nid, init, .. } => {
                    let x = if let Some(init) = init {
                        let px = spot_lookup.get(&lookup_nid(init)).unwrap();
                        let px = px.borrow().position.x;
                        px + XSIZE
                    } else {
                        0.0
                    };
                    let s = &mut *spot.borrow_mut();
                    s.set_position(x, lookup_y((x / XSIZE) as usize) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                }
                Node::Next {
                    nid, state, next, ..
                } => {
                    let lx = spot_lookup.get(&lookup_nid(state)).unwrap();
                    let lx = lx.borrow().position.x;
                    let rx = spot_lookup.get(&lookup_nid(next)).unwrap();
                    let rx = rx.borrow().position.x;
                    let x: u64 = (max(lx as u64, rx as u64) / XSIZE as u64) + 1;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                    leaves.push(spot.clone());
                }
                Node::Bad { nid, cond, .. } => {
                    let px = spot_lookup.get(&lookup_nid(cond)).unwrap();
                    let px = px.borrow().position.x;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(
                        px + XSIZE,
                        lookup_y(((px + XSIZE) / XSIZE) as usize) as f32 * YSIZE,
                    );

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                    leaves.push(spot.clone());
                }
                Node::Comment(_) => unreachable!(),
            };
        }

        Self {
            tick: 0,
            spot_lookup,
            spot_list,
            leaves,
        }
    }

    pub fn draw(&self, ui: &mut Ui) {
        let translation = ui.min_rect().min;
        // TODO: draw edges
        for spot in &self.spot_list {
            let s = &*spot.borrow();
            let inner_size = Vec2::from([
                XSIZE - 2.0 * NODE_MARGIN - 2.0 * NODE_PADDING,
                YSIZE - 2.0 * NODE_MARGIN - 2.0 * NODE_PADDING,
            ]);
            let outer_size = Vec2::from([XSIZE - 2.0 * NODE_MARGIN, YSIZE - 2.0 * NODE_MARGIN]);
            let inner_pos = translation
                + s.position.to_vec2()
                + Vec2::from([NODE_MARGIN + NODE_PADDING, NODE_MARGIN + NODE_PADDING]);
            let outer_pos =
                translation + s.position.to_vec2() + Vec2::from([NODE_MARGIN, NODE_MARGIN]);
            let inner_rect = Rect::from_min_size(inner_pos, inner_size);
            let outer_rect = Rect::from_min_size(outer_pos, outer_size);

            let mut child_ui = ui.child_ui(inner_rect, Layout::left_to_right(Align::TOP));
            let painter = child_ui.painter();
            painter.rect_filled(outer_rect, Rounding::from(5.0), Color32::from_gray(40));
            child_ui.put(inner_rect, s.clone());
        }
    }
}

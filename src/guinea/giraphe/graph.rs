use crate::guinea::giraphe::{Giraphe, Spot, Value};
use crate::unicorn::{Model, Nid, Node, NodeRef};
use egui::epaint::CubicBezierShape;
use egui::{Align, Color32, Layout, Pos2, Rect, Rounding, Stroke, Ui, Vec2};
use log::trace;
use std::cmp::max;
use std::collections::HashMap;
use std::iter::zip;

static XSIZE: f32 = 150.0;
static YSIZE: f32 = 200.0;
static NODE_MARGIN: f32 = 10.0;
static NODE_PADDING: f32 = 5.0;

// TODO:
//   inputs in the graph
//   preprocess the graph
//    - collapse if then else block
//    - collapse input gathering
//    - unroll once to remove all unnecessary extras
//   better layout:
//    - directly dependant nodes near each other
//    - less density
impl Giraphe {
    pub fn from(model: &Model) -> Self {
        assert!(
            !model.lines.is_empty(),
            "Can't convert model before it was renumbered!"
        );

        let mut spot_lookup = HashMap::new();
        let mut spot_list = Vec::new();
        let mut leaves = Vec::new();
        let mut inputs = Vec::new();

        let mut states = Vec::new();

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
                Node::Input { nid, .. } => {
                    let s = &mut *spot.borrow_mut();
                    s.set_position(0.0, lookup_y(0) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                    inputs.push(spot.clone());
                }
                Node::Const { nid, .. } => {
                    let s = &mut *spot.borrow_mut();
                    s.set_position(0.0, lookup_y(0) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                }

                // one parent
                Node::Not { nid, value, .. } | Node::Ext { nid, value, .. } => {
                    let px = spot_lookup.get(&map_node_ref_to_nid(value)).unwrap();
                    let px = px.borrow().position.x;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(
                        px + XSIZE,
                        lookup_y(((px + XSIZE) / XSIZE) as usize) as f32 * YSIZE,
                    );

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
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
                    let lx = spot_lookup.get(&map_node_ref_to_nid(left)).unwrap();
                    let lx = lx.borrow().position.x;
                    let rx = spot_lookup.get(&map_node_ref_to_nid(right)).unwrap();
                    let rx = rx.borrow().position.x;
                    let x: u64 = (max(lx as u64, rx as u64) / XSIZE as u64) + 1;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
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
                    let lx = spot_lookup.get(&map_node_ref_to_nid(one)).unwrap();
                    let lx = lx.borrow().position.x;
                    let rx = spot_lookup.get(&map_node_ref_to_nid(two)).unwrap();
                    let rx = rx.borrow().position.x;
                    let cx = spot_lookup.get(&map_node_ref_to_nid(three)).unwrap();
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
                        let px = spot_lookup.get(&map_node_ref_to_nid(init)).unwrap();
                        let px = px.borrow().position.x;
                        px + XSIZE
                    } else {
                        0.0
                    };
                    let s = &mut *spot.borrow_mut();
                    s.set_position(x, lookup_y((x / XSIZE) as usize) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                    if init.is_none() {
                        inputs.push(spot.clone());
                    } else {
                        states.push(spot.clone());
                    }
                }
                Node::Next {
                    nid, state, next, ..
                } => {
                    let lx = spot_lookup.get(&map_node_ref_to_nid(state)).unwrap();
                    let lx = lx.borrow().position.x;
                    let rx = spot_lookup.get(&map_node_ref_to_nid(next)).unwrap();
                    let rx = rx.borrow().position.x;
                    let x: u64 = (max(lx as u64, rx as u64) / XSIZE as u64) + 1;
                    let s = &mut *spot.borrow_mut();
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(spot.clone());
                    spot_lookup.insert(*nid, spot.clone());
                    leaves.push(spot.clone());
                }
                Node::Bad { nid, cond, .. } => {
                    let px = spot_lookup.get(&map_node_ref_to_nid(cond)).unwrap();
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

        states.sort_by(|x, y| {
            let x = &*x.borrow();
            let y = &*y.borrow();
            let r = match (&*x.origin.borrow(), &*y.origin.borrow()) {
                (Node::State { name: t1, .. }, Node::State { name: t2, .. }) => t1.cmp(t2),
                _ => unreachable!(),
            };
            r
        });

        let mut g = Self {
            tick: 0,
            spot_lookup,
            spot_list,
            leaves,
            inputs,
            states: states.clone(),
            pan: Vec2::default(),
        };

        g.tick = -1;
        for si in states {
            let si = &mut *si.borrow_mut();
            if let Node::State { init, .. } = &*si.origin.borrow() {
                let init = map_node_ref_to_nid(init.as_ref().unwrap());
                let init = &mut *g.spot_lookup.get(&init).unwrap().borrow_mut();
                si.val_cur = init.evaluate(&g);
            } else {
                panic!("Can't initialize non state node")
            };
        }
        g.tick = 0;

        g
    }

    pub fn draw(&mut self, ui: &mut Ui) {
        let translation = ui.min_rect().min + self.pan;

        // draw edges
        for spot in &self.spot_list {
            let s = &*spot.borrow();
            let outer_pos =
                translation + s.position.to_vec2() + Vec2::from([NODE_MARGIN, NODE_MARGIN]);
            let outer_size = Vec2::from([XSIZE - 2.0 * NODE_MARGIN, YSIZE - 2.0 * NODE_MARGIN]);
            let outer_rect = Rect::from_min_size(outer_pos, outer_size);
            if !ui.is_rect_visible(outer_rect) {
                continue;
            }

            match &*s.origin.borrow() {
                // zero parents
                Node::Const { .. } | Node::Input { .. } => {
                    // nothing to draw
                }
                // one parent
                Node::Not { nid, value, .. }
                | Node::Ext { nid, value, .. }
                | Node::Bad {
                    nid, cond: value, ..
                } => {
                    let outport = self.calc_outport(value, translation);
                    let inport = self.calc_inport(nid, translation, 0.5);

                    ui.painter().add(bezzyfy(outport, inport));
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
                }
                | Node::Next {
                    nid,
                    state: left,
                    next: right,
                    ..
                } => {
                    let out1 = self.calc_outport(left, translation);
                    let out2 = self.calc_outport(right, translation);
                    let in1 = self.calc_inport(nid, translation, 1.0 / 3.0);
                    let in2 = self.calc_inport(nid, translation, 2.0 / 3.0);

                    ui.painter().add(bezzyfy(out1, in1));
                    ui.painter().add(bezzyfy(out2, in2));
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
                    let out1 = self.calc_outport(one, translation);
                    let out2 = self.calc_outport(two, translation);
                    let out3 = self.calc_outport(three, translation);
                    let in1 = self.calc_inport(nid, translation, 0.25);
                    let in2 = self.calc_inport(nid, translation, 0.5);
                    let in3 = self.calc_inport(nid, translation, 0.75);

                    ui.painter().add(bezzyfy(out1, in1));
                    ui.painter().add(bezzyfy(out2, in2));
                    ui.painter().add(bezzyfy(out3, in3));
                }
                // special cases
                Node::State { nid, init, .. } => {
                    if let Some(value) = init {
                        let out1 = self.calc_outport(value, translation);
                        let in1 = self.calc_inport(nid, translation, 0.5);

                        ui.painter().add(bezzyfy(out1, in1));
                    }
                }
                Node::Comment(_) => unreachable!(),
            };
        }

        // draw nodes
        for spot in &self.spot_list {
            let s = &*spot.borrow();
            let outer_size = Vec2::from([XSIZE - 2.0 * NODE_MARGIN, YSIZE - 2.0 * NODE_MARGIN]);
            let outer_pos =
                translation + s.position.to_vec2() + Vec2::from([NODE_MARGIN, NODE_MARGIN]);
            let outer_rect = Rect::from_min_size(outer_pos, outer_size);

            if !ui.is_rect_visible(outer_rect) {
                continue;
            }

            let inner_size = Vec2::from([
                XSIZE - 2.0 * NODE_MARGIN - 2.0 * NODE_PADDING,
                YSIZE - 2.0 * NODE_MARGIN - 2.0 * NODE_PADDING,
            ]);
            let inner_pos = translation
                + s.position.to_vec2()
                + Vec2::from([NODE_MARGIN + NODE_PADDING, NODE_MARGIN + NODE_PADDING]);
            let inner_rect = Rect::from_min_size(inner_pos, inner_size);

            let mut child_ui = ui.child_ui(inner_rect, Layout::left_to_right(Align::TOP));
            let painter = child_ui.painter();
            painter.rect_filled(outer_rect, Rounding::from(5.0), Color32::from_gray(40));
            child_ui.put(inner_rect, s.clone());
        }
    }

    pub fn interact(&mut self, ui: &mut Ui) {
        if ui.rect_contains_pointer(ui.min_rect()) && ui.ctx().input().pointer.primary_down() {
            self.pan += ui.ctx().input().pointer.delta();
        }
    }

    fn calc_inport(&self, n: &Nid, translation: Pos2, pos: f32) -> Pos2 {
        let sin = &*self.spot_lookup.get(n).unwrap().borrow();
        translation + sin.position.to_vec2() + Vec2::from([NODE_MARGIN, YSIZE * pos])
    }

    fn calc_outport(&self, n: &NodeRef, translation: Pos2) -> Pos2 {
        let out = &*self
            .spot_lookup
            .get(&map_node_ref_to_nid(n))
            .unwrap()
            .borrow();
        translation + out.position.to_vec2() + Vec2::from([XSIZE - NODE_MARGIN, YSIZE * 0.5])
    }

    pub fn tick_over(&mut self) -> isize {
        self.tick += 1;

        let res: Vec<_> = self
            .leaves
            .iter()
            .map(|x| {
                let s = &mut *x.borrow_mut();
                s.evaluate(self)
            })
            .collect();

        for (sp, val) in zip(&self.leaves, res) {
            let sp = &mut *sp.borrow_mut();
            match &*sp.origin.borrow() {
                Node::Next { state, .. } => {
                    let state = map_node_ref_to_nid(state);
                    let state = self.spot_lookup.get(&state).unwrap();
                    let state = &mut *state.borrow_mut();
                    state.val_cur = val;
                }
                Node::Bad { name, .. } => {
                    if sp.val_cur == Value::Boolean(true) {
                        println!("Bad is true: {}", name.as_ref().unwrap());
                    }
                }
                _ => unreachable!("Only Bad and Next nodes can be leaves"),
            };
        }

        self.tick
    }
}

fn bezzyfy(src: Pos2, dest: Pos2) -> CubicBezierShape {
    let stroke = Stroke::from((5.0, Color32::from_gray(255)));
    let control_scale = ((src.x - dest.x) / 2.0).max(30.0);
    let vout_control = src + Vec2::X * control_scale;
    let sin_control = dest - Vec2::X * control_scale;

    CubicBezierShape::from_points_stroke(
        [src, vout_control, sin_control, dest],
        false,
        Color32::TRANSPARENT,
        stroke,
    )
}

pub fn map_node_ref_to_nid(n: &NodeRef) -> Nid {
    match &*n.borrow() {
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
    }
}

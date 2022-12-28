use std::cmp::max;
use std::collections::HashMap;
use std::default::Default;
use std::iter::zip;

use egui::epaint::CubicBezierShape;
use egui::{Align, Color32, Layout, Pos2, Rect, Rounding, Stroke, Ui, Vec2};
use log::trace;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Array, Bitvector, Boolean};
use crate::guinea::giraphe::{Giraphe, MachineWord, Spot, Value};
use crate::unicorn::{Model, Nid, Node, NodeRef};

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

        let mut spot_lookup: HashMap<Nid, Spot> = HashMap::new();
        let mut spot_list: Vec<Nid> = Vec::new();
        let mut leaves: Vec<Nid> = Vec::new();
        let mut inputs: Vec<Nid> = Vec::new();

        let mut states: Vec<Nid> = Vec::new();
        let mut registers: [Option<Nid>; 32] = Default::default();

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
                    let mut s = spot;
                    s.set_position(0.0, lookup_y(0) as f32 * YSIZE);

                    spot_list.push(*nid);
                    inputs.push(*nid);
                    spot_lookup.insert(*nid, s);
                }
                Node::Const { nid, .. } => {
                    let mut s = spot;
                    s.set_position(0.0, lookup_y(0) as f32 * YSIZE);

                    spot_list.push(*nid);
                    spot_lookup.insert(*nid, s);
                }

                // one parent
                Node::Not { nid, value, .. } | Node::Ext { nid, value, .. } => {
                    let px = spot_lookup.get(&map_node_ref_to_nid(value)).unwrap();
                    let px = px.position.x;
                    let mut s = spot;
                    s.set_position(
                        px + XSIZE,
                        lookup_y(((px + XSIZE) / XSIZE) as usize) as f32 * YSIZE,
                    );

                    spot_list.push(*nid);
                    spot_lookup.insert(*nid, s);
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
                    let lx = lx.position.x;
                    let rx = spot_lookup.get(&map_node_ref_to_nid(right)).unwrap();
                    let rx = rx.position.x;
                    let x: u64 = (max(lx as u64, rx as u64) / XSIZE as u64) + 1;
                    let mut s = spot;
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(*nid);
                    spot_lookup.insert(*nid, s);
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
                    let lx = lx.position.x;
                    let rx = spot_lookup.get(&map_node_ref_to_nid(two)).unwrap();
                    let rx = rx.position.x;
                    let cx = spot_lookup.get(&map_node_ref_to_nid(three)).unwrap();
                    let cx = cx.position.x;
                    let x = max(lx as u64, rx as u64);
                    let x: u64 = (max(x, cx as u64) / XSIZE as u64) + 1;
                    let mut s = spot;
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(*nid);
                    spot_lookup.insert(*nid, s);
                }
                // special cases
                Node::State {
                    nid, init, name, ..
                } => {
                    let x = if let Some(init) = init {
                        let px = spot_lookup.get(&map_node_ref_to_nid(init)).unwrap();
                        let px = px.position.x;
                        px + XSIZE
                    } else {
                        0.0
                    };
                    let mut s = spot;
                    s.set_position(x, lookup_y((x / XSIZE) as usize) as f32 * YSIZE);

                    spot_list.push(*nid);
                    if init.is_none() {
                        inputs.push(*nid);
                    } else {
                        states.push(*nid);
                    }

                    Self::map_to_reg_spot(&mut registers, *nid, name.as_ref().unwrap().as_str());

                    spot_lookup.insert(*nid, s);
                }
                Node::Next {
                    nid, state, next, ..
                } => {
                    let lx = spot_lookup.get(&map_node_ref_to_nid(state)).unwrap();
                    let lx = lx.position.x;
                    let rx = spot_lookup.get(&map_node_ref_to_nid(next)).unwrap();
                    let rx = rx.position.x;
                    let x: u64 = (max(lx as u64, rx as u64) / XSIZE as u64) + 1;
                    let mut s = spot;
                    s.set_position(x as f32 * XSIZE, lookup_y(x as usize) as f32 * YSIZE);

                    spot_list.push(*nid);
                    leaves.push(*nid);
                    spot_lookup.insert(*nid, s);
                }
                Node::Bad { nid, cond, .. } => {
                    let px = spot_lookup.get(&map_node_ref_to_nid(cond)).unwrap();
                    let px = px.position.x;
                    let mut s = spot;
                    s.set_position(
                        px + XSIZE,
                        lookup_y(((px + XSIZE) / XSIZE) as usize) as f32 * YSIZE,
                    );

                    spot_list.push(*nid);
                    leaves.push(*nid);
                    spot_lookup.insert(*nid, s);
                }
                Node::Comment(_) => unreachable!(),
            };
        }

        states.sort_by(|x, y| {
            let x = spot_lookup.get(x).unwrap();
            let y = spot_lookup.get(y).unwrap();
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
            registers,
            is_ascii: false,
            input: String::default(),
            states: states.clone(),
            pan: Vec2::default(),
            input_queue: vec![],
        };

        g.tick = -1;
        for si in states {
            let node_ref = {
                let si = g.spot_lookup.get(&si).unwrap();
                si.origin.clone()
            };

            if let Node::State { init, .. } = &*node_ref.borrow() {
                let init = map_node_ref_to_nid(init.as_ref().unwrap());
                let value = g.evaluate(&init);
                let si = g.spot_lookup.get_mut(&si).unwrap();
                si.set_value(value);
            } else {
                panic!("Can't initialize non state node")
            };
        }
        g.tick = 0;

        g
    }

    fn map_to_reg_spot(arr: &mut [Option<Nid>; 32], spot: Nid, str: &str) {
        match str {
            "zero" => arr[0] = Some(spot),
            "ra" => arr[1] = Some(spot),
            "sp" => arr[2] = Some(spot),
            "gp" => arr[3] = Some(spot),
            "tp" => arr[4] = Some(spot),
            "t0" => arr[5] = Some(spot),
            "t1" => arr[6] = Some(spot),
            "t2" => arr[7] = Some(spot),
            "s0" => arr[8] = Some(spot),
            "s1" => arr[9] = Some(spot),
            "a0" => arr[10] = Some(spot),
            "a1" => arr[11] = Some(spot),
            "a2" => arr[12] = Some(spot),
            "a3" => arr[13] = Some(spot),
            "a4" => arr[14] = Some(spot),
            "a5" => arr[15] = Some(spot),
            "a6" => arr[16] = Some(spot),
            "a7" => arr[17] = Some(spot),
            "s2" => arr[18] = Some(spot),
            "s3" => arr[19] = Some(spot),
            "s4" => arr[20] = Some(spot),
            "s5" => arr[21] = Some(spot),
            "s6" => arr[22] = Some(spot),
            "s7" => arr[23] = Some(spot),
            "s8" => arr[24] = Some(spot),
            "s9" => arr[25] = Some(spot),
            "s10" => arr[26] = Some(spot),
            "s11" => arr[27] = Some(spot),
            "t3" => arr[28] = Some(spot),
            "t4" => arr[29] = Some(spot),
            "t5" => arr[30] = Some(spot),
            "t6" => arr[31] = Some(spot),
            _ => {}
        }
    }

    pub fn draw(&mut self, ui: &mut Ui) {
        let translation = ui.min_rect().min + self.pan;

        // draw edges
        for spot in &self.spot_list {
            let s = self.spot_lookup.get(spot).unwrap();
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
            let s = self.spot_lookup.get_mut(spot).unwrap();
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
            child_ui.put(inner_rect, Spot::from_spot(s));
        }
    }

    pub fn interact(&mut self, ui: &mut Ui) {
        if ui.rect_contains_pointer(ui.min_rect()) && ui.ctx().input().pointer.primary_down() {
            self.pan += ui.ctx().input().pointer.delta();
        }
    }

    fn calc_inport(&self, n: &Nid, translation: Pos2, pos: f32) -> Pos2 {
        let sin = self.nid_to_spot(n);
        translation + sin.position.to_vec2() + Vec2::from([NODE_MARGIN, YSIZE * pos])
    }

    fn calc_outport(&self, n: &NodeRef, translation: Pos2) -> Pos2 {
        let out = self.nid_to_spot(&map_node_ref_to_nid(n));
        translation + out.position.to_vec2() + Vec2::from([XSIZE - NODE_MARGIN, YSIZE * 0.5])
    }

    pub fn tick_over(&mut self) -> isize {
        self.tick += 1;

        let leaves = self.leaves.clone();
        let mut res = Vec::new();
        for leaf in leaves {
            let value = self.evaluate(&leaf);
            res.push(value);
        }

        for (sp, val) in zip(&self.leaves, res) {
            let (node_ref, val_cur) = {
                let s = self.nid_to_spot(sp);
                (s.origin.clone(), s.val_cur.clone())
            };

            match &*node_ref.borrow() {
                Node::Next { state, .. } => {
                    let state = map_node_ref_to_nid(state);
                    let state = self.spot_lookup.get_mut(&state).unwrap();
                    state.set_value(val);
                }
                Node::Bad { name, .. } => {
                    if val_cur == Boolean(true) {
                        println!("Bad is true: {}", name.as_ref().unwrap());
                    }
                }
                _ => unreachable!("Only Bad and Next nodes can be leaves"),
            };
        }

        self.tick
    }

    pub(crate) fn nid_to_spot(&self, nid: &Nid) -> &Spot {
        self.spot_lookup.get(nid).unwrap()
    }

    pub fn evaluate(&mut self, nid: &Nid) -> Value {
        {
            let mut spot = self.spot_lookup.get_mut(nid).unwrap();

            if self.tick == spot.tick {
                return spot.val_cur.clone();
            }
            spot.tick = if self.tick > 0 { self.tick } else { 0 };
            spot.val_old = spot.val_cur.clone();
        }

        let (node_ref, val_cur) = {
            let spot = self.nid_to_spot(nid);
            (spot.origin.clone(), spot.val_cur.clone())
        };

        let val = {
            let x = match &*node_ref.borrow() {
                Node::Const { .. } => val_cur,
                Node::Read {
                    memory, address, ..
                } => {
                    let memory = &map_node_ref_to_nid(memory);
                    let memory = self.evaluate(memory);
                    let address = &map_node_ref_to_nid(address);
                    match (&memory, &self.evaluate(address)) {
                        (Array(m), Bitvector(i)) => Bitvector(*m.get(i).unwrap()),
                        _ => unreachable!(),
                    }
                }
                Node::Write {
                    nid,
                    memory,
                    address,
                    value,
                    ..
                } => {
                    let memory = &map_node_ref_to_nid(memory);
                    let address = &map_node_ref_to_nid(address);
                    let value = &map_node_ref_to_nid(value);

                    match (
                        self.evaluate(memory),
                        self.evaluate(address),
                        self.evaluate(value),
                    ) {
                        (Array(mut m), Bitvector(i), Bitvector(x)) => {
                            m.insert(i, x);
                            Array(m)
                        }
                        x => unreachable!("caused by {} {:?}", nid, x),
                    }
                }
                Node::Add { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) + self.evaluate(spot2)
                }
                Node::Sub { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) - self.evaluate(spot2)
                }
                Node::Mul { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) * self.evaluate(spot2)
                }
                Node::Div { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) / self.evaluate(spot2)
                }
                Node::Rem { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) % self.evaluate(spot2)
                }
                Node::Sll { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) << self.evaluate(spot2)
                }
                Node::Srl { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) >> self.evaluate(spot2)
                }
                Node::Ult { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    Boolean(self.evaluate(spot1) < self.evaluate(spot2))
                }
                Node::Ext { value, .. } => {
                    let spot = &map_node_ref_to_nid(value);
                    let v = self.evaluate(spot);
                    if let Boolean(b) = v {
                        Bitvector(Concrete(u64::from(b)))
                    } else {
                        v
                    }
                }
                Node::Ite {
                    cond, left, right, ..
                } => {
                    let cond = &map_node_ref_to_nid(cond);
                    match &self.evaluate(cond) {
                        Boolean(b) => {
                            if *b {
                                let left = &map_node_ref_to_nid(left);
                                self.evaluate(left)
                            } else {
                                let right = &map_node_ref_to_nid(right);
                                self.evaluate(right)
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                Node::Eq { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    Boolean(self.evaluate(spot1) == self.evaluate(spot2))
                }
                Node::And { left, right, .. } => {
                    let spot1 = &map_node_ref_to_nid(left);
                    let spot2 = &map_node_ref_to_nid(right);
                    self.evaluate(spot1) & self.evaluate(spot2)
                }
                Node::Not { value, .. } => {
                    let spot = &map_node_ref_to_nid(value);
                    !self.evaluate(spot)
                }
                Node::State { .. } => val_cur,
                Node::Next { next, .. } => {
                    let spot = &map_node_ref_to_nid(next);
                    self.evaluate(spot)
                }
                Node::Input { .. } => val_cur,
                Node::Bad { cond, .. } => {
                    let spot = &map_node_ref_to_nid(cond);
                    self.evaluate(spot)
                }
                Node::Comment(_) => unreachable!(),
            };
            x
        };

        let mut spot = self.spot_lookup.get_mut(nid).unwrap();

        spot.val_cur = val.clone();

        val
    }

    pub fn system_state(
        &self,
    ) -> (
        Vec<Value>,
        Option<String>,
        bool,
        HashMap<MachineWord, MachineWord>,
    ) {
        let regs = self
            .registers
            .as_ref()
            .iter()
            .map(|x| {
                if let Some(x) = x {
                    let s = self.nid_to_spot(x);
                    s.val_cur.clone()
                } else {
                    Bitvector(Concrete(0))
                }
            })
            .collect::<Vec<Value>>();

        let mut pc = None;
        let mut vm = HashMap::new();
        let mut kernel_mode = false;

        for x in &self.states {
            let s = self.nid_to_spot(x);
            match &*s.origin.borrow() {
                Node::State { name, .. } => {
                    let name = name.as_ref().unwrap().as_str();
                    if name == "virtual-memory" {
                        if let Array(hm) = &s.val_cur {
                            vm = hm.clone();
                        }
                    }

                    if name.starts_with("pc=") && s.val_cur == Boolean(true) {
                        if pc.is_some() {
                            panic!("Multiple PCs active at once: {:?} and {:?}", pc, x);
                        }
                        pc = Some(String::from(&name[3..]));
                    }

                    if name.starts_with("kernel") {
                        kernel_mode |= Boolean(true) == s.val_cur;
                    }
                }
                _ => unreachable!(),
            };
        }

        (regs, pc, kernel_mode, vm)
    }

    pub fn a7_is_read_or_exit(&self) -> bool {
        self.nid_to_spot(&self.registers[17].unwrap()).val_cur == Bitvector(Concrete(63))
            || self.nid_to_spot(&self.registers[17].unwrap()).val_cur == Bitvector(Concrete(93))
    }

    pub fn is_in_kernel_mode(&self) -> bool {
        self.states
            .iter()
            .map(|x| self.nid_to_spot(x))
            .filter(|x| match &*x.origin.borrow() {
                Node::State { name, .. } => name.as_ref().unwrap().starts_with("kernel"),
                _ => unreachable!(),
            })
            .map(|x| x.val_cur == Boolean(true))
            .reduce(|a, x| a || x)
            .unwrap()
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

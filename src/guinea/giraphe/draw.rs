use egui::epaint::{CubicBezierShape, QuadraticBezierShape};
use egui::{Color32, Direction, Pos2, Rect, Response, RichText, Rounding, Stroke, Ui, Vec2};
use indexmap::IndexMap;

use crate::guinea::giraphe::graph::noderef_to_nid;
use crate::guinea::giraphe::LayoutNode::Real;
use crate::guinea::giraphe::{Giraphe, Spot};
use crate::unicorn::{Nid, Node};

static X_SPACING: f32 = 50.0;
static Y_SPACING: f32 = 100.0;
static NODE_SIZE: f32 = 30.0;

impl Giraphe {
    pub fn draw(&mut self, ui: &mut Ui) {
        let top_left = ui.min_rect().min.to_vec2() + Vec2::from([100.0, 100.0]) + self.pan;

        let mut nodes_to_draw = IndexMap::<Nid, Rect>::new();
        // determine nodes to draw
        for nid in self.node_lookup.keys() {
            let pos = self.layout.positions.get(&Real(*nid)).unwrap();

            let rect = Rect::from_center_size(
                Pos2::from([pos.x * X_SPACING, pos.y * Y_SPACING]) + top_left,
                Vec2::from([NODE_SIZE, NODE_SIZE]),
            );

            if ui.min_rect().contains_rect(rect) {
                nodes_to_draw.insert(*nid, rect);
            }
        }

        let mut nodes_drawn = IndexMap::<Nid, ()>::new();
        for (nid, rect) in &nodes_to_draw {
            for parent in self.node_to_children.get(nid).unwrap() {
                let p1 = rect.center();
                let p2 = self.layout.positions.get(&Real(*parent)).unwrap();
                let p2 = Pos2::from((p2.x * X_SPACING, p2.y * Y_SPACING)) + top_left;

                let control_points = self
                    .layout
                    .edges_to_its_dummies
                    .get(&(Real(*parent), Real(*nid)));

                if let Some(control_points) = control_points {
                    if control_points.len() > 1 {
                        let control1 = control_points.first().unwrap();
                        let control2 = control_points.last().unwrap();
                        let control1 = self.layout.positions.get(control1).unwrap();
                        let control1 =
                            Pos2::from((control1.x * X_SPACING, control1.y * Y_SPACING)) + top_left;
                        let control2 = self.layout.positions.get(control2).unwrap();
                        let control2 =
                            Pos2::from((control2.x * X_SPACING, control2.y * Y_SPACING)) + top_left;
                        let curve = CubicBezierShape::from_points_stroke(
                            [p1, control1, control2, p2],
                            false,
                            Color32::TRANSPARENT,
                            Stroke::from((5.0, Color32::from_gray(255))),
                        );
                        ui.painter().add(curve);
                    } else {
                        let control = control_points.first().unwrap();
                        let control = self.layout.positions.get(control).unwrap();
                        let control =
                            Pos2::from((control.x * X_SPACING, control.y * Y_SPACING)) + top_left;
                        let curve = QuadraticBezierShape::from_points_stroke(
                            [p1, control, p2],
                            false,
                            Color32::TRANSPARENT,
                            Stroke::from((5.0, Color32::from_gray(255))),
                        );
                        ui.painter().add(curve);
                    }
                } else {
                    ui.painter()
                        .line_segment([p1, p2], Stroke::from((5.0, Color32::from_gray(255))));
                }
            }
            nodes_drawn.insert(*nid, ());
        }

        for (nid, rect) in nodes_to_draw {
            let spot = self.node_lookup.get(&nid).unwrap();
            ui.painter()
                .rect_filled(rect, Rounding::from(NODE_SIZE / 2.0), spot.color());
            let mut child_ui = ui.child_ui(
                rect,
                egui::Layout::centered_and_justified(Direction::LeftToRight),
            );
            self.draw_spot(spot, &mut child_ui);
        }
    }

    fn draw_spot(&self, spot: &Spot, ui: &mut Ui) -> Response {
        ui.label(
            RichText::new(spot.display_value_abbreviated())
                .monospace()
                .color(Color32::from_gray(255)),
        )
        .on_hover_ui(|ui| self.draw_spot_on_hover(spot, ui))
    }

    fn draw_spot_on_hover(&self, spot: &Spot, ui: &mut Ui) {
        ui.heading(spot.title());
        let node_name = spot.node_name();
        if let Some(node_name) = node_name {
            ui.label(node_name);
        }

        ui.add_space(5.0);
        ui.label(format!("Current value: {}", spot.display_value()));

        let operation = self.display_operation(spot);
        if let Some(operation) = operation {
            ui.label(RichText::new("Operation:").underline());
            ui.label(operation);
        }
    }

    fn display_operation(&self, spot: &Spot) -> Option<String> {
        match &*spot.origin.borrow() {
            Node::Const { .. } => Some(format!("Constant: {}", spot.display_value())),
            Node::Read {
                memory, address, ..
            } => {
                let memory = self.node_lookup.get(&noderef_to_nid(memory)).unwrap();
                let address = self.node_lookup.get(&noderef_to_nid(address)).unwrap();
                Some(format!(
                    "{}[{}] = {}",
                    memory.display_value(),
                    address.display_value(),
                    spot.display_value()
                ))
            }
            Node::Write {
                memory,
                address,
                value,
                ..
            } => {
                let memory = self.node_lookup.get(&noderef_to_nid(memory)).unwrap();
                let address = self.node_lookup.get(&noderef_to_nid(address)).unwrap();
                let value = self.node_lookup.get(&noderef_to_nid(value)).unwrap();
                Some(format!(
                    "{}[{}] = {} => {}",
                    memory.display_value(),
                    address.display_value(),
                    value.display_value(),
                    spot.display_value()
                ))
            }
            Node::Add { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} + {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Sub { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} - {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Mul { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} * {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Div { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} / {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Rem { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} % {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Sll { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} << {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Srl { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} >> {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Ult { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} < {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Ext { value, .. } => {
                let value = self.node_lookup.get(&noderef_to_nid(value)).unwrap();
                Some(format!(
                    "{} extended to {}",
                    value.display_value(),
                    spot.display_value()
                ))
            }
            Node::Ite {
                cond, left, right, ..
            } => {
                let cond = self.node_lookup.get(&noderef_to_nid(cond)).unwrap();
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "if {} then {} else {} => {}",
                    cond.display_value(),
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Eq { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} == {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::And { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} & {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Not { value, .. } => {
                let value = self.node_lookup.get(&noderef_to_nid(value)).unwrap();
                Some(format!(
                    "!{} = {}",
                    value.display_value(),
                    spot.display_value()
                ))
            }
            Node::State { .. } => None,
            Node::Next { state, .. } => {
                let state = self.node_lookup.get(&noderef_to_nid(state)).unwrap();
                Some(format!(
                    "{} will become {}",
                    state.display_value(),
                    spot.display_value()
                ))
            }
            Node::Input { .. } => None,
            Node::Bad { .. } => None,
            Node::Comment(_) => unreachable!(),
            Node::Divu { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} / {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
            Node::Or { left, right, .. } => {
                let left = self.node_lookup.get(&noderef_to_nid(left)).unwrap();
                let right = self.node_lookup.get(&noderef_to_nid(right)).unwrap();
                Some(format!(
                    "{} | {} = {}",
                    left.display_value(),
                    right.display_value(),
                    spot.display_value()
                ))
            }
        }
    }
}

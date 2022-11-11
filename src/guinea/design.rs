use egui::style::Margin;
use egui::{Color32, Frame, Rounding, Stroke};

pub fn get_frame_design() -> Frame {
    Frame {
        inner_margin: Margin::symmetric(8.0, 8.0),
        rounding: Rounding::none(),
        fill: Color32::from_gray(27),
        stroke: Stroke::new(1.0, Color32::from_gray(60)),
        ..Default::default()
    }
}

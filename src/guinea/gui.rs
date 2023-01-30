use crate::guinea::{cli2gui, model2graph, Guineacorn, Use};
use eframe::egui;
use std::default::Default;

pub fn gui() {
    let options = eframe::NativeOptions {
        initial_window_size: Some(egui::vec2(1600.0, 900.0)),
        ..Default::default()
    };
    eframe::run_native(
        "Guineacorn",
        options,
        Box::new(|_cc| Box::<Guineacorn>::default()),
    );
}

impl eframe::App for Guineacorn {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        if self.error.is_some() {
            egui::Window::new("Error Occured")
                .fixed_pos((350.0, 200.0))
                .fixed_size((400.0, 200.0))
                .resizable(false)
                .collapsible(false)
                .show(ctx, |ui| {
                    ui.label(self.error.as_ref().unwrap().to_string());
                    if ui.button("OK").clicked() {
                        self.error = None;
                    }
                });
        }

        egui::SidePanel::right("Selection")
            .resizable(false)
            .width_range(1000.0..=1000.0)
            .frame(get_frame_design())
            .show(ctx, |ui| match self.using {
                Use::Cli2Gui => cli2gui::output_window(self, ui),
                Use::NodeGraph => model2graph::output_window(self, ui),
            });

        egui::TopBottomPanel::top("Use")
            .frame(get_frame_design())
            .resizable(false)
            .show(ctx, |ui| {
                ui.horizontal_wrapped(|ui| {
                    ui.selectable_value(&mut self.using, Use::Cli2Gui, "Cli2Gui");
                    ui.selectable_value(&mut self.using, Use::NodeGraph, "Node Graph");
                })
            });

        egui::CentralPanel::default()
            .frame(get_frame_design())
            .show(ctx, |ui| match self.using {
                Use::Cli2Gui => cli2gui::input_window(self, ui),
                Use::NodeGraph => model2graph::input_window(self, ui),
            });
    }
}

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

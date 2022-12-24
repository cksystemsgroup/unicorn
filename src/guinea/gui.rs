#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release

use crate::guinea::design::get_frame_design;
use crate::guinea::{cli2gui, model2graph, Guineacorn, Use};
use eframe::egui;
use image;
use std::default::Default;

pub fn gui() {
    let icon = image::open("src/guinea/icon.png")
        .expect("Failed to open icon path")
        .to_rgba8();
    let (icon_width, icon_height) = icon.dimensions();

    let options = eframe::NativeOptions {
        initial_window_size: Some(egui::vec2(1000.0, 650.0)),
        icon_data: Some(eframe::IconData {
            rgba: icon.into_raw(),
            width: icon_width,
            height: icon_height,
        }),
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
        // error popup
        let error_msg = self.error_message.clone();
        egui::Window::new("Error Occured")
            .fixed_pos((350.0, 200.0))
            .fixed_size((400.0, 200.0))
            .resizable(false)
            .collapsible(false)
            .open(&mut self.error_occurred)
            .show(ctx, |ui| ui.label(error_msg.unwrap()));

        egui::SidePanel::right("Selection")
            .resizable(false)
            .width_range(600.0..=600.0)
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

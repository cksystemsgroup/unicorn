#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release

use std::default::Default;
use std::io::BufWriter;
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::str::FromStr;
use std::vec::Vec;

use bytesize::ByteSize;
use eframe::egui;
use egui::Ui;
use rfd;
use riscu::load_object_file;

use crate::guinea::design::get_frame_design;
use crate::guinea::error_handling::unpanic;
use crate::unicorn::builder::generate_model;
use crate::unicorn::{write_model, Model};

pub fn gui() {
    let options = eframe::NativeOptions {
        initial_window_size: Some(egui::vec2(1000.0, 600.0)),
        ..Default::default()
    };
    eframe::run_native(
        "Guineacorn",
        options,
        Box::new(|_cc| Box::new(MyApp::default())),
    );
}

struct MyApp {
    model: Option<Model>,
    memory_size: u64,
    max_heap: u32,
    max_stack: u32,
    picked_path: Option<String>,
    output: Option<String>,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            model: None,
            memory_size: 1,
            max_heap: 8,
            max_stack: 32,
            picked_path: None,
            output: None,
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::SidePanel::left("Selection")
            .frame(get_frame_design())
            .resizable(false)
            .width_range(400.0..=400.0)
            .show(ctx, |ui| {
                self.input_window(ui);
            });
        egui::CentralPanel::default()
            .frame(get_frame_design())
            .show(ctx, |ui| {
                self.output_window(ui);
            });
    }
}

impl MyApp {
    fn input_window(&mut self, ui: &mut Ui) {
        ui.heading("Input");
        ui.separator();
        ui.wrap_text();
        ui.add_space(10.0);

        ui.horizontal_wrapped(|ui| {
            ui.label("Select a file to start.");
            if ui.button("Open file...").clicked() {
                if let Some(path) = rfd::FileDialog::new().pick_file() {
                    self.picked_path = Some(path.display().to_string());
                }
            }
        });

        ui.collapsing("Advanced Settings", |ui| {
            ui.horizontal_wrapped(|ui| {
                ui.label("Number of machine-words usable as heap.");
                ui.add(egui::DragValue::new(&mut self.max_heap));
            });
            ui.horizontal_wrapped(|ui| {
                ui.label("Number of machine-words usable as stack.");
                ui.add(egui::DragValue::new(&mut self.max_stack));
            });
            ui.horizontal_wrapped(|ui| {
                ui.label("Total size of memory in MiB.");
                ui.add(egui::DragValue::new(&mut self.memory_size).clamp_range(1..=1024));
            });
        });

        if let Some(picked_path) = &self.picked_path.clone() {
            ui.horizontal_wrapped(|ui| {
                ui.label("Selected File:");
                ui.monospace(picked_path);
            });

            if ui.button("Create Model").clicked() {
                let path = PathBuf::from_str(picked_path).unwrap();
                let program = load_object_file(&path);

                if let Ok(..) = program {
                    let mut error_msg = "".to_string();
                    let mut model = None;
                    let mut output = None;

                    let program = program.unwrap();
                    unpanic(
                        AssertUnwindSafe(|| {
                            generate_model(
                                &program,
                                ByteSize::mib(self.memory_size).as_u64(),
                                self.max_heap,
                                self.max_stack,
                                &[picked_path.clone()],
                            )
                        }),
                        |m| {
                            let mut buf = BufWriter::new(Vec::new());
                            let mo = m.unwrap();
                            let _ = write_model(&mo, &mut buf);
                            let bytes = buf.into_inner().unwrap();
                            let stri = String::from_utf8(bytes).unwrap();
                            output = Some(stri);
                            model = Some(mo);
                        },
                        &mut error_msg,
                    );

                    self.model = model;

                    if !error_msg.is_empty() {
                        self.output = Some(format!(
                            "Trying to create the model failed an assert:\n{}",
                            error_msg
                        ));
                    } else {
                        self.output = output;
                    }
                } else {
                    self.output = Some(format!(
                        "Invalid file, gave error:\n{:?}",
                        program.err().unwrap()
                    ))
                }
            }
        };
    }

    fn output_window(&self, ui: &mut Ui) {
        ui.heading("Output");
        ui.separator();
        egui::ScrollArea::vertical()
            .auto_shrink([false; 2])
            .show(ui, |ui| match &self.output {
                Some(output) => ui
                    .with_layout(egui::Layout::left_to_right(egui::Align::TOP), |ui| {
                        ui.monospace(output)
                    }),
                _ => ui.with_layout(
                    egui::Layout::centered_and_justified(egui::Direction::TopDown),
                    |ui| ui.label("Nothing to show."),
                ),
            });
    }
}

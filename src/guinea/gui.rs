#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release

use crate::unicorn::builder::generate_model;
use crate::unicorn::write_model;
use bytesize::ByteSize;
use eframe::egui;
use rfd;
use riscu::load_object_file;
use std::io::BufWriter;
use std::path::PathBuf;
use std::str::FromStr;
use std::vec::Vec;
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
    _model: Option<String>,
    memory_size: u64,
    max_heap: u32,
    max_stack: u32,
    picked_path: Option<String>,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            _model: None,
            memory_size: ByteSize::mib(1).as_u64(),
            max_heap: 8,
            max_stack: 32,
            picked_path: None,
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            // file dialog
            ui.label("Select File");
            if ui.button("Open file...").clicked() {
                if let Some(path) = rfd::FileDialog::new().pick_file() {
                    self.picked_path = Some(path.display().to_string());
                }
            }

            if let Some(picked_path) = &self.picked_path {
                ui.horizontal(|ui| {
                    ui.label("Picked File:");
                    ui.monospace(picked_path);
                });

                if ui.button("Load File").clicked() {
                    let path = PathBuf::from_str(picked_path).unwrap();
                    let program = load_object_file(&path).unwrap();
                    let mut buf = BufWriter::new(Vec::new());
                    let model = generate_model(
                        &program,
                        self.memory_size,
                        self.max_heap,
                        self.max_stack,
                        &[picked_path.clone()],
                    );
                    write_model(&model.unwrap(), &mut buf).expect("TODO: panic message");
                    let bytes = buf.into_inner().unwrap();
                    let stri = String::from_utf8(bytes).unwrap();
                    self._model = Some(stri);
                }
                egui::ScrollArea::vertical().show(ui, |ui| {
                    if let Some(model) = &self._model {
                        ui.label(model);
                    }
                });
            }

            // end file dialog
        });
    }
}

#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release

use std::default::Default;
use std::fs;
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::str::FromStr;

use bytesize::ByteSize;
use eframe::egui;
use egui::Ui;
use rfd;
use riscu::load_object_file;

use crate::guinea::design::get_frame_design;
use crate::guinea::error_handling::unpanic;
use crate::guinea::print::{stringify_model, stringify_program};
use crate::unicorn::btor2file_parser::parse_btor2_file;
use crate::unicorn::builder::generate_model;
use crate::unicorn::memory::replace_memory;
use crate::unicorn::optimize::optimize_model;
use crate::unicorn::solver::none_impl;
use crate::unicorn::unroller::{prune_model, renumber_model, unroll_model};
use crate::unicorn::Model;

// TODO:
//   -b, --bitblast            Perform bitblasting of the model
//   -d, --dimacs              Output DIMACS CNF instead of BTOR2
//   -e, --emulate             Start emulation from created model
//   -c, --compile             Compile program from created model
//   -i, --inputs <inputs>     Concrete inputs to specialize the model
//   -s, --solver <SOLVER>     SMT solver used for optimization [default: generic] [possible values: generic]
//   preview file & error messages as floating windows

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
    model_created: bool,
    bit_blasted: bool,
    pruned: bool,
    from_beator: bool,
    extras: String,
    times_unrolled: usize,
    desired_unrolls: usize,
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
            model_created: false,
            bit_blasted: false,
            pruned: false,
            from_beator: false,
            extras: "".to_string(),
            times_unrolled: 0,
            desired_unrolls: 0,
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
        ui.separator();
        ui.wrap_text();
        ui.add_space(10.0);

        ui.label("Selecting Input");
        ui.separator();

        ui.horizontal_wrapped(|ui| {
            ui.label("Select a file to start.");
            if ui.button("Open file...").clicked() {
                self.reset_model_params();
                if let Some(path) = rfd::FileDialog::new().pick_file() {
                    self.picked_path = Some(path.display().to_string());
                }
            }
        });

        ui.checkbox(
            &mut self.from_beator,
            "Input is a BTOR2 file (currently broken)",
        );

        ui.add_space(5.0);
        ui.label("Arguments passed to emulated program");
        ui.text_edit_singleline(&mut self.extras);
        ui.add_space(5.0);

        let picked_path = self
            .picked_path
            .clone()
            .unwrap_or_else(|| "NONE".to_string());

        ui.horizontal_wrapped(|ui| {
            ui.label("Selected File:");
            ui.monospace(&picked_path);
        });

        ui.add_space(10.0);
        ui.add_enabled_ui(self.picked_path.is_some(), |ui| {
            if ui.button("Preview File").clicked() {
                self.reset_model_params();
                let path = PathBuf::from_str(&picked_path).unwrap();

                self.output = if !self.from_beator {
                    Some(match load_object_file(&path) {
                        Ok(x) => stringify_program(&x),
                        Err(e) => format!("Invalid file, gave error:\n{:?}", e),
                    })
                } else {
                    let model = parse_btor2_file(&path);
                    Some(stringify_model(&model))
                }
            }

            ui.add_space(20.0);
            ui.label("Model Creation");
            ui.separator();

            ui.add_enabled_ui(!self.model_created, |ui| {
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

            ui.add_space(10.0);

            ui.add_enabled_ui(!self.model_created, |ui| {
                if ui.button("Create Model").clicked() {
                    self.model_created = true;

                    let picked_path = self.picked_path.as_ref().unwrap().clone();

                    let path = PathBuf::from_str(&picked_path).unwrap();
                    let program = load_object_file(&path);

                    if let Ok(..) = program {
                        let mut error_msg = "".to_string();
                        let mut model = None;
                        let mut output = None;

                        let program = program.unwrap();
                        unpanic(
                            AssertUnwindSafe(|| {
                                let argv = [
                                    vec![picked_path.clone()],
                                    self.extras.split(' ').map(String::from).collect(),
                                ]
                                .concat();
                                generate_model(
                                    &program,
                                    ByteSize::mib(self.memory_size).as_u64(),
                                    self.max_heap,
                                    self.max_stack,
                                    &argv,
                                )
                            }),
                            |m| {
                                let mo = m.unwrap();
                                output = Some(stringify_model(&mo));
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
            });

            ui.add_space(20.0);
            ui.label("Model modification");
            ui.separator();

            ui.add_enabled_ui(self.model.is_some(), |ui| {
                ui.add_enabled_ui(!(self.bit_blasted || self.pruned), |ui| {
                    ui.horizontal_wrapped(|ui| {
                        ui.label("Number of unrolls:");
                        ui.add(egui::DragValue::new(&mut self.desired_unrolls));
                    });
                    if ui.button("Do Unrolls").clicked() {
                        self.model.as_mut().unwrap().lines.clear();
                        replace_memory(self.model.as_mut().unwrap());

                        self.times_unrolled += self.desired_unrolls;

                        for n in 0..self.desired_unrolls {
                            unroll_model(self.model.as_mut().unwrap(), n);
                        }

                        self.desired_unrolls = 0;

                        // TODO: support all optimizers
                        prune_model(self.model.as_mut().unwrap());
                        optimize_model::<none_impl::NoneSolver>(self.model.as_mut().unwrap());
                        renumber_model(self.model.as_mut().unwrap());
                        self.output = Some(stringify_model(self.model.as_ref().unwrap()));
                    }
                    ui.label(format!("({} done so far)", self.times_unrolled));
                });

                ui.horizontal_wrapped(|ui| {
                    ui.add_enabled_ui(!(self.pruned || self.bit_blasted), |ui| {
                        if ui.button("Prune").clicked() {
                            self.pruned = true;
                            // TODO: support all optimizers
                            optimize_model::<none_impl::NoneSolver>(self.model.as_mut().unwrap());
                            renumber_model(self.model.as_mut().unwrap());
                            self.output = Some(stringify_model(self.model.as_ref().unwrap()));
                        }
                    });

                    ui.add_enabled_ui(self.bit_blasted, |ui| {
                        if ui.button("Bit Blast").clicked() {
                            self.bit_blasted = true;
                        }
                    });
                });
            });

            ui.add_space(20.0);
            ui.label("Output Handling");
            ui.separator();
            ui.add_enabled_ui(self.output.is_some(), |ui| {
                if ui.button("Save Output").clicked() {
                    let path = std::env::current_dir().unwrap();
                    let res = rfd::FileDialog::new()
                        .set_file_name("output.btor2")
                        .set_directory(&path)
                        .save_file();

                    if let Some(save_file) = res {
                        fs::write(save_file, self.output.as_ref().unwrap()).ok();
                    }
                }
            });
        });
    }

    fn output_window(&self, ui: &mut Ui) {
        ui.heading("Output");
        ui.separator();
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

    fn reset_model_params(&mut self) {
        self.model_created = false;
        self.bit_blasted = false;
        self.pruned = false;
        self.times_unrolled = 0;
    }
}

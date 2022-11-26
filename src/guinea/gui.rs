#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release

use std::default::Default;
use std::io::BufWriter;
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::mpsc::{Receiver, Sender};
use std::thread::JoinHandle;
use std::time::Duration;
use std::{fs, thread};

use bytesize::ByteSize;
use eframe::egui;
use egui::Ui;
use rfd;
use riscu::load_object_file;

use crate::cli::SmtType;
use crate::guinea::design::get_frame_design;
use crate::guinea::error_handling::{fix_memory, unpanic};
use crate::guinea::print::{stringify_model, stringify_program};
use crate::unicorn::bitblasting::{bitblast_model, GateModel};
use crate::unicorn::bitblasting_dimacs::write_dimacs_model;
use crate::unicorn::bitblasting_printer::write_btor2_model;
use crate::unicorn::btor2file_parser::{parse_btor2_file, parse_btor2_string};
use crate::unicorn::builder::generate_model;
use crate::unicorn::memory::replace_memory;
use crate::unicorn::optimize::{optimize_model_with_input, optimize_model_with_solver};
#[cfg(feature = "boolector")]
use crate::unicorn::solver::boolector_impl;
use crate::unicorn::solver::none_impl;
#[cfg(feature = "z3")]
use crate::unicorn::solver::z3solver_impl;
use crate::unicorn::unroller::{prune_model, renumber_model, unroll_model};
use crate::unicorn::Model;

// TODO:
//   minimize input

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
    bit_model: Option<GateModel>,
    picked_path: Option<String>,
    output: Option<String>,
    model_created: bool,
    bit_blasted: bool,
    pruned: bool,
    from_beator: bool,
    extras: String,
    times_unrolled: usize,
    desired_unrolls: usize,
    dimacs: bool,
    solver: SmtType,
    error_message: Option<String>,
    error_occurred: bool,
    unroller: Option<JoinHandle<String>>,
    memory_data: MemoryData,
    loading_data: LoadingData,
    minimize: bool,
    timeout: Option<Duration>,
}

#[derive(Clone)]
pub struct MemoryData {
    pub memory_size: u64,
    pub max_heap: u32,
    pub max_stack: u32,
    pub data_start: u64,
    pub data_end: u64,
}

#[derive(Default)]
struct LoadingData {
    message: String,
    progress: f32,
    maximum: f32,
    progress_receiver: Option<Receiver<f32>>,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            model: None,
            bit_model: None,
            picked_path: None,
            output: None,
            model_created: false,
            bit_blasted: false,
            pruned: false,
            from_beator: false,
            extras: "".to_string(),
            times_unrolled: 0,
            desired_unrolls: 0,
            dimacs: false,
            solver: SmtType::Generic,
            error_message: None,
            error_occurred: false,
            unroller: None,
            memory_data: MemoryData {
                memory_size: 1,
                data_start: 0,
                data_end: 0,
                max_heap: 8,
                max_stack: 32,
            },
            loading_data: LoadingData::default(),
            minimize: false,
            timeout: None,
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        let error_msg = self.error_message.clone();

        if self.unroller.is_some() && self.unroller.as_ref().unwrap().is_finished() {
            let unroller = std::mem::replace(&mut self.unroller, None);
            let serial_model = unroller.unwrap().join().unwrap();
            let mut model = parse_btor2_string(&serial_model);
            fix_memory(&mut model, &self.memory_data);
            renumber_model(&mut model);

            self.unroller = None;
            self.model = Some(model);
            self.output = Some(stringify_model(self.model.as_ref().unwrap()));
        }

        egui::Window::new("Error Occured")
            .open(&mut self.error_occurred)
            .fixed_pos((350.0, 200.0))
            .fixed_size((400.0, 200.0))
            .resizable(false)
            .collapsible(false)
            .show(ctx, |ui| ui.label(error_msg.as_ref().unwrap()));

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
            ui.checkbox(&mut self.from_beator, "Input is a BTOR2 file");
        });

        let picked_path = self
            .picked_path
            .clone()
            .unwrap_or_else(|| "NONE".to_string());

        ui.add_space(10.0);
        ui.add_enabled_ui(self.picked_path.is_some(), |ui| {
            ui.label("Selected File:");
            ui.monospace(&picked_path);

            if ui.button("Preview File").clicked() {
                self.reset_model_params();
                let path = PathBuf::from_str(&picked_path).unwrap();

                if !self.from_beator {
                    match load_object_file(&path) {
                        Ok(x) => self.output = Some(stringify_program(&x)),
                        Err(e) => {
                            self.error_occurred = true;
                            self.error_message =
                                Some(format!("Invalid file, gave error:\n{:?}", e));
                            self.reset_model_params();
                        }
                    };
                } else {
                    let mut model = parse_btor2_file(&path);
                    renumber_model(&mut model);
                    self.output = Some(stringify_model(&model));
                }
            }

            ui.add_space(15.0);
            ui.label("Model Creation");
            ui.separator();

            ui.add_enabled_ui(!self.model_created, |ui| {
                ui.horizontal_wrapped(|ui| {
                    ui.label("Number of machine-words usable as heap.");
                    ui.add(egui::DragValue::new(&mut self.memory_data.max_heap));
                });
                ui.horizontal_wrapped(|ui| {
                    ui.label("Number of machine-words usable as stack.");
                    ui.add(egui::DragValue::new(&mut self.memory_data.max_stack));
                });
                ui.horizontal_wrapped(|ui| {
                    ui.label("Total size of memory in MiB.");
                    ui.add(
                        egui::DragValue::new(&mut self.memory_data.memory_size)
                            .clamp_range(1..=1024),
                    );
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
                                self.memory_data.data_start = program.data.address;
                                self.memory_data.data_end =
                                    program.data.address + program.data.content.len() as u64;
                                generate_model(
                                    &program,
                                    ByteSize::mib(self.memory_data.memory_size).as_u64(),
                                    self.memory_data.max_heap,
                                    self.memory_data.max_stack,
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
                            self.error_occurred = true;
                            self.error_message = Some(format!(
                                "Trying to create the model failed an assert:\n{}",
                                error_msg
                            ));
                            self.reset_model_params();
                        } else {
                            self.output = output;
                        }
                    } else {
                        self.error_occurred = true;
                        self.error_message = Some(format!(
                            "Invalid file, gave error:\n{:?}",
                            program.err().unwrap()
                        ));
                        self.reset_model_params();
                    }
                }
            });

            ui.add_space(15.0);
            ui.label("Model modification");
            ui.separator();

            ui.add_enabled_ui(self.model.is_some(), |ui| {
                ui.add_enabled_ui(!(self.bit_blasted || self.pruned), |ui| {
                    ui.horizontal_wrapped(|ui| {
                        ui.label("Number of unrolls:");
                        ui.add(egui::DragValue::new(&mut self.desired_unrolls));
                        if ui.button("Do Unrolls").clicked() {
                            let serial_model = stringify_model(self.model.as_ref().unwrap());
                            let desired_unrolls = self.desired_unrolls;
                            let extras = self.extras.clone();
                            let solver = self.solver.clone();
                            let memory_data = self.memory_data.clone();
                            let minimize = self.minimize;
                            let timeout = self.timeout;

                            self.loading_data.maximum = self.desired_unrolls as f32;
                            self.loading_data.message = "Unrolling Model".to_string();

                            self.times_unrolled += self.desired_unrolls;
                            self.desired_unrolls = 0;
                            self.output = None;
                            self.model = None;

                            let (sender, receiver): (Sender<f32>, Receiver<f32>) =
                                std::sync::mpsc::channel();
                            self.loading_data.progress_receiver = Some(receiver);

                            self.unroller = Some(
                                thread::Builder::new()
                                    .stack_size(64 * 1024 * 1024) // increase thread stack size to avoid stack overflow
                                    .spawn(move || {
                                        let mut model = parse_btor2_string(&serial_model);
                                        fix_memory(&mut model, &memory_data);
                                        model.lines.clear();
                                        replace_memory(&mut model);

                                        for n in 0..desired_unrolls {
                                            unroll_model(&mut model, n);
                                            if !extras.is_empty() {
                                                optimize_model_with_input(
                                                    &mut model,
                                                    &mut extras
                                                        .split(' ')
                                                        .map(|x| x.parse().unwrap_or(0))
                                                        .collect(),
                                                )
                                            }
                                            sender
                                                .send(n as f32)
                                                .expect("Could not send progress.");
                                        }

                                        match solver {
                                            SmtType::Generic => {
                                                optimize_model_with_solver::<none_impl::NoneSolver>(
                                                    &mut model, timeout, minimize,
                                                )
                                            }
                                            #[cfg(feature = "boolector")]
                                            SmtType::Boolector => optimize_model_with_solver::<
                                                boolector_impl::BoolectorSolver,
                                            >(
                                                &mut model, timeout, minimize
                                            ),
                                            #[cfg(feature = "z3")]
                                            SmtType::Z3 => optimize_model_with_solver::<
                                                z3solver_impl::Z3SolverWrapper,
                                            >(
                                                &mut model, timeout, minimize
                                            ),
                                        }

                                        renumber_model(&mut model);
                                        stringify_model(&model)
                                    })
                                    .unwrap(),
                            );
                        }
                        ui.label(format!("({} done so far)", self.times_unrolled));
                    });

                    ui.add_space(10.0);
                    ui.label("Optimizer:");
                    ui.horizontal_wrapped(|ui| {
                        ui.selectable_value(&mut self.solver, SmtType::Generic, "Generic");
                        #[cfg(feature = "boolector")]
                        ui.selectable_value(&mut self.solver, SmtType::Boolector, "Boolector");
                        #[cfg(feature = "z3")]
                        ui.selectable_value(&mut self.solver, SmtType::Z3, "Z3");
                    });
                    ui.add_space(5.0);
                    ui.label("Concrete inputs passed to optimizer:");
                    ui.text_edit_singleline(&mut self.extras);
                    ui.add_space(5.0);
                });

                ui.add_enabled_ui(!(self.pruned || self.bit_blasted), |ui| {
                    if ui.button("Prune Sequential Part").clicked() {
                        self.pruned = true;
                        prune_model(self.model.as_mut().unwrap());

                        match self.solver {
                            SmtType::Generic => {
                                optimize_model_with_solver::<none_impl::NoneSolver>(
                                    self.model.as_mut().unwrap(),
                                    self.timeout,
                                    self.minimize,
                                )
                            }
                            #[cfg(feature = "boolector")]
                            SmtType::Boolector => {
                                optimize_model_with_solver::<boolector_impl::BoolectorSolver>(
                                    self.model.as_mut().unwrap(),
                                    self.timeout,
                                    self.minimize,
                                )
                            }
                            #[cfg(feature = "z3")]
                            SmtType::Z3 => {
                                optimize_model_with_solver::<z3solver_impl::Z3SolverWrapper>(
                                    self.model.as_mut().unwrap(),
                                    self.timeout,
                                    self.minimize,
                                )
                            }
                        }
                        renumber_model(self.model.as_mut().unwrap());
                        self.output = Some(stringify_model(self.model.as_ref().unwrap()));
                    }
                });

                ui.add_space(5.0);
                ui.add_enabled_ui(!self.bit_blasted, |ui| {
                    ui.horizontal_wrapped(|ui| {
                        if ui.button("Bit Blast").clicked() {
                            let mut buf = BufWriter::new(Vec::new());

                            self.bit_blasted = true;
                            self.bit_model =
                                Some(bitblast_model(self.model.as_ref().unwrap(), true, 64));
                            let _ = if self.dimacs {
                                write_dimacs_model(self.bit_model.as_ref().unwrap(), &mut buf)
                            } else {
                                write_btor2_model(self.bit_model.as_ref().unwrap(), &mut buf)
                            };
                            let bytes = buf.into_inner().unwrap();
                            self.output = Some(String::from_utf8(bytes).unwrap());
                        }
                        ui.checkbox(&mut self.dimacs, "Output dimacs gate model");
                    });
                });
            });

            ui.add_space(15.0);
            ui.label("Output Handling");
            ui.separator();
            ui.add_enabled_ui(self.output.is_some(), |ui| {
                ui.horizontal_wrapped(|ui| {
                    if ui.button("Save Output").clicked() {
                        let path = std::env::current_dir().unwrap();
                        let res = rfd::FileDialog::new()
                            .set_file_name(if self.dimacs {
                                "output.cnf"
                            } else {
                                "output.btor2"
                            })
                            .set_directory(&path)
                            .save_file();

                        if let Some(save_file) = res {
                            fs::write(save_file, self.output.as_ref().unwrap()).ok();
                        }
                    }

                    if ui.button("Reset Model").clicked() {
                        self.model = None;
                        self.output = None;
                        self.reset_model_params();
                    }
                });
            });
        });
    }

    fn output_window(&mut self, ui: &mut Ui) {
        ui.heading("Output");
        ui.separator();
        ui.separator();

        if self.unroller.is_some() {
            ui.vertical_centered_justified(|ui| {
                ui.add(egui::Spinner::new());
                ui.label(format!(
                    "{}... ({}/{})",
                    self.loading_data.message,
                    self.loading_data.progress,
                    self.loading_data.maximum
                ));
                self.loading_data.progress = self
                    .loading_data
                    .progress_receiver
                    .as_ref()
                    .unwrap()
                    .try_recv()
                    .unwrap_or(self.loading_data.progress);

                if self.loading_data.progress >= self.loading_data.maximum - 2.0 {
                    self.loading_data.message = "Renumbering model".to_string();
                }

                ui.add(
                    egui::ProgressBar::new(self.loading_data.progress / self.loading_data.maximum)
                        .show_percentage()
                        .desired_width(200.0),
                );
            });
        } else {
            egui::ScrollArea::vertical()
                .auto_shrink([false; 2])
                .show(ui, |ui| {
                    match &self.output {
                        Some(output) => ui
                            .with_layout(egui::Layout::left_to_right(egui::Align::TOP), |ui| {
                                ui.monospace(output)
                            }),
                        _ => ui.with_layout(
                            egui::Layout::centered_and_justified(egui::Direction::TopDown),
                            |ui| ui.label("Nothing to show."),
                        ),
                    };
                });
        }
    }

    fn reset_model_params(&mut self) {
        self.model_created = false;
        self.bit_blasted = false;
        self.pruned = false;
        self.times_unrolled = 0;
        self.unroller = None;
        self.model = None;
        self.output = None;
    }
}

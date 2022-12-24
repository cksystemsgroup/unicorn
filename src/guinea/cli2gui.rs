use crate::cli::SmtType;
use crate::guinea::error_handling::{fix_memory, unpanic};
use crate::guinea::print::{stringify_model, stringify_program};
use crate::guinea::Guineacorn;
use crate::unicorn::bitblasting::{bitblast_model, GateModel};
use crate::unicorn::bitblasting_dimacs::write_dimacs_model;
use crate::unicorn::bitblasting_printer::write_btor2_model;
use crate::unicorn::btor2file_parser::{parse_btor2_file, parse_btor2_string};
use crate::unicorn::builder::generate_model;
use crate::unicorn::memory::replace_memory;
use crate::unicorn::optimize::{optimize_model_with_input, optimize_model_with_solver};
#[cfg(feature = "boolector")]
use crate::unicorn::smt_solver::boolector_impl;
use crate::unicorn::smt_solver::none_impl;
#[cfg(feature = "z3")]
use crate::unicorn::smt_solver::z3solver_impl;
use crate::unicorn::unroller::{prune_model, renumber_model, unroll_model};
use bytesize::ByteSize;
use egui::Ui;
use riscu::load_object_file;
use std::io::BufWriter;
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::mpsc::{Receiver, Sender};
use std::thread::JoinHandle;
use std::time::Duration;
use std::{fs, thread};

pub struct Cli2Gui {
    pub bit_model: Option<GateModel>,
    pub bit_blasted: bool,
    pub pruned: bool,
    pub from_beator: bool,
    pub extras: String,
    pub times_unrolled: usize,
    pub desired_unrolls: usize,
    pub dimacs: bool,
    pub solver: SmtType,
    pub unroller: Option<JoinHandle<String>>,
    pub minimize: bool,
    pub timeout: Option<Duration>,
}

impl Default for Cli2Gui {
    fn default() -> Self {
        Self {
            bit_model: None,
            bit_blasted: false,
            pruned: false,
            from_beator: false,
            extras: "".to_string(),
            times_unrolled: 0,
            desired_unrolls: 0,
            dimacs: false,
            solver: SmtType::Generic,
            unroller: None,
            minimize: false,
            timeout: None,
        }
    }
}

// TODO:
//   minimize input
pub fn input_window(data: &mut Guineacorn, ui: &mut Ui) {
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
            data.reset_model_params();
            if let Some(path) = rfd::FileDialog::new().pick_file() {
                data.picked_path = Some(path.display().to_string());
            }
        }
        ui.checkbox(&mut data.cli2gui.from_beator, "Input is a BTOR2 file");
    });

    let picked_path = data
        .picked_path
        .clone()
        .unwrap_or_else(|| "NONE".to_string());

    ui.add_space(10.0);
    ui.add_enabled_ui(data.picked_path.is_some(), |ui| {
        ui.label("Selected File:");
        ui.monospace(&picked_path);

        if ui.button("Preview File").clicked() {
            data.reset_model_params();
            let path = PathBuf::from_str(&picked_path).unwrap();

            if !data.cli2gui.from_beator {
                match load_object_file(&path) {
                    Ok(x) => data.output = Some(stringify_program(&x)),
                    Err(e) => {
                        data.error_occurred = true;
                        data.error_message = Some(format!("Invalid file, gave error:\n{:?}", e));
                        data.reset_model_params();
                    }
                };
            } else {
                let mut model = parse_btor2_file(&path);
                renumber_model(&mut model);
                data.output = Some(stringify_model(&model));
            }
        }

        ui.add_space(15.0);
        ui.label("Model Creation");
        ui.separator();

        ui.add_enabled_ui(!data.model_created, |ui| {
            ui.horizontal_wrapped(|ui| {
                ui.label("Number of machine-words usable as heap.");
                ui.add(egui::DragValue::new(&mut data.memory_data.max_heap));
            });
            ui.horizontal_wrapped(|ui| {
                ui.label("Number of machine-words usable as stack.");
                ui.add(egui::DragValue::new(&mut data.memory_data.max_stack));
            });
            ui.horizontal_wrapped(|ui| {
                ui.label("Total size of memory in MiB.");
                ui.add(
                    egui::DragValue::new(&mut data.memory_data.memory_size).clamp_range(1..=1024),
                );
            });
        });

        ui.add_space(10.0);

        ui.add_enabled_ui(!data.model_created, |ui| {
            if ui.button("Create Model").clicked() {
                data.model_created = true;

                let picked_path = data.picked_path.as_ref().unwrap().clone();

                let path = PathBuf::from_str(&picked_path).unwrap();
                let program = load_object_file(path);

                if let Ok(..) = program {
                    let mut error_msg = "".to_string();
                    let mut model = None;
                    let mut output = None;

                    let program = program.unwrap();
                    unpanic(
                        AssertUnwindSafe(|| {
                            let argv = [
                                vec![picked_path.clone()],
                                data.cli2gui.extras.split(' ').map(String::from).collect(),
                            ]
                            .concat();
                            data.memory_data.data_start = program.data.address;
                            data.memory_data.data_end =
                                program.data.address + program.data.content.len() as u64;
                            generate_model(
                                &program,
                                ByteSize::mib(data.memory_data.memory_size).as_u64(),
                                data.memory_data.max_heap,
                                data.memory_data.max_stack,
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

                    data.model = model;

                    if !error_msg.is_empty() {
                        data.error_occurred = true;
                        data.error_message = Some(format!(
                            "Trying to create the model failed an assert:\n{}",
                            error_msg
                        ));
                        data.reset_model_params();
                    } else {
                        data.output = output;
                    }
                } else {
                    data.error_occurred = true;
                    data.error_message = Some(format!(
                        "Invalid file, gave error:\n{:?}",
                        program.err().unwrap()
                    ));
                    data.reset_model_params();
                }
            }
        });

        ui.add_space(15.0);
        ui.label("Model modification");
        ui.separator();

        ui.add_enabled_ui(data.model.is_some(), |ui| {
            ui.add_enabled_ui(!(data.cli2gui.bit_blasted || data.cli2gui.pruned), |ui| {
                ui.horizontal_wrapped(|ui| {
                    ui.label("Number of unrolls:");
                    ui.add(egui::DragValue::new(&mut data.cli2gui.desired_unrolls));
                    if ui.button("Do Unrolls").clicked() {
                        let serial_model = stringify_model(data.model.as_ref().unwrap());
                        let desired_unrolls = data.cli2gui.desired_unrolls;
                        let extras = data.cli2gui.extras.clone();
                        let solver = data.cli2gui.solver.clone();
                        let memory_data = data.memory_data.clone();
                        let minimize = data.cli2gui.minimize;
                        let timeout = data.cli2gui.timeout;

                        data.loading_data.maximum = data.cli2gui.desired_unrolls as f32;
                        data.loading_data.message = "Unrolling Model".to_string();

                        data.cli2gui.times_unrolled += data.cli2gui.desired_unrolls;
                        data.cli2gui.desired_unrolls = 0;
                        data.output = None;
                        data.model = None;

                        let (sender, receiver): (Sender<f32>, Receiver<f32>) =
                            std::sync::mpsc::channel();
                        data.loading_data.progress_receiver = Some(receiver);

                        data.cli2gui.unroller = Some(
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
                                        sender.send(n as f32).expect("Could not send progress.");
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
                    ui.label(format!("({} done so far)", data.cli2gui.times_unrolled));
                });

                ui.add_space(10.0);
                ui.label("Optimizer:");
                ui.horizontal_wrapped(|ui| {
                    ui.selectable_value(&mut data.cli2gui.solver, SmtType::Generic, "Generic");
                    #[cfg(feature = "boolector")]
                    ui.selectable_value(&mut data.cli2gui.solver, SmtType::Boolector, "Boolector");
                    #[cfg(feature = "z3")]
                    ui.selectable_value(&mut data.cli2gui.solver, SmtType::Z3, "Z3");
                });
                ui.add_space(5.0);
                ui.label("Concrete inputs passed to optimizer:");
                ui.text_edit_singleline(&mut data.cli2gui.extras);
                ui.add_space(5.0);
            });

            ui.add_enabled_ui(!(data.cli2gui.pruned || data.cli2gui.bit_blasted), |ui| {
                if ui.button("Prune Sequential Part").clicked() {
                    data.cli2gui.pruned = true;
                    prune_model(data.model.as_mut().unwrap());

                    match data.cli2gui.solver {
                        SmtType::Generic => optimize_model_with_solver::<none_impl::NoneSolver>(
                            data.model.as_mut().unwrap(),
                            data.cli2gui.timeout,
                            data.cli2gui.minimize,
                        ),
                        #[cfg(feature = "boolector")]
                        SmtType::Boolector => {
                            optimize_model_with_solver::<boolector_impl::BoolectorSolver>(
                                data.model.as_mut().unwrap(),
                                data.cli2gui.timeout,
                                data.cli2gui.minimize,
                            )
                        }
                        #[cfg(feature = "z3")]
                        SmtType::Z3 => {
                            optimize_model_with_solver::<z3solver_impl::Z3SolverWrapper>(
                                data.model.as_mut().unwrap(),
                                data.cli2gui.timeout,
                                data.cli2gui.minimize,
                            )
                        }
                    }
                    renumber_model(data.model.as_mut().unwrap());
                    data.output = Some(stringify_model(data.model.as_ref().unwrap()));
                }
            });

            ui.add_space(5.0);
            ui.add_enabled_ui(!data.cli2gui.bit_blasted, |ui| {
                ui.horizontal_wrapped(|ui| {
                    if ui.button("Bit Blast").clicked() {
                        let mut buf = BufWriter::new(Vec::new());

                        data.cli2gui.bit_blasted = true;
                        data.cli2gui.bit_model =
                            Some(bitblast_model(data.model.as_ref().unwrap(), true, 64));
                        let _ = if data.cli2gui.dimacs {
                            write_dimacs_model(data.cli2gui.bit_model.as_ref().unwrap(), &mut buf)
                        } else {
                            write_btor2_model(data.cli2gui.bit_model.as_ref().unwrap(), &mut buf)
                        };
                        let bytes = buf.into_inner().unwrap();
                        data.output = Some(String::from_utf8(bytes).unwrap());
                    }
                    ui.checkbox(&mut data.cli2gui.dimacs, "Output dimacs gate model");
                });
            });
        });

        ui.add_space(15.0);
        ui.label("Output Handling");
        ui.separator();
        ui.add_enabled_ui(data.output.is_some(), |ui| {
            ui.horizontal_wrapped(|ui| {
                if ui.button("Save Output").clicked() {
                    let path = std::env::current_dir().unwrap();
                    let res = rfd::FileDialog::new()
                        .set_file_name(if data.cli2gui.dimacs {
                            "output.cnf"
                        } else {
                            "output.btor2"
                        })
                        .set_directory(path)
                        .save_file();

                    if let Some(save_file) = res {
                        fs::write(save_file, data.output.as_ref().unwrap()).ok();
                    }
                }

                if ui.button("Reset Model").clicked() {
                    data.model = None;
                    data.output = None;
                    data.reset_model_params();
                }
            });
        });
    });
}

pub fn output_window(data: &mut Guineacorn, ui: &mut Ui) {
    if data.cli2gui.unroller.is_some() && data.cli2gui.unroller.as_ref().unwrap().is_finished() {
        let unroller = std::mem::replace(&mut data.cli2gui.unroller, None);
        let serial_model = unroller.unwrap().join().unwrap();
        let mut model = parse_btor2_string(&serial_model);
        fix_memory(&mut model, &data.memory_data);
        renumber_model(&mut model);

        data.cli2gui.unroller = None;
        data.model = Some(model);
        data.output = Some(stringify_model(data.model.as_ref().unwrap()));
    }

    ui.heading("Output");
    ui.separator();
    ui.separator();

    if data.cli2gui.unroller.is_some() {
        ui.vertical_centered_justified(|ui| {
            ui.add(egui::Spinner::new());
            ui.label(format!(
                "{}... ({}/{})",
                data.loading_data.message, data.loading_data.progress, data.loading_data.maximum
            ));
            data.loading_data.progress = data
                .loading_data
                .progress_receiver
                .as_ref()
                .unwrap()
                .try_recv()
                .unwrap_or(data.loading_data.progress);

            if data.loading_data.progress >= data.loading_data.maximum - 2.0 {
                data.loading_data.message = "Renumbering model".to_string();
            }

            ui.add(
                egui::ProgressBar::new(data.loading_data.progress / data.loading_data.maximum)
                    .show_percentage()
                    .desired_width(200.0),
            );
        });
    } else {
        egui::ScrollArea::vertical()
            .auto_shrink([false; 2])
            .show(ui, |ui| {
                match &data.output {
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

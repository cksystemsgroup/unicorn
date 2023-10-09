use std::io::BufWriter;
use std::sync::mpsc::{Receiver, Sender};
use std::{fs, thread};

use anyhow::Error;
use egui::Ui;

use unicorn::disassemble::Disassembly;

use crate::cli::SmtType;
use crate::guinea::components::general;
use crate::guinea::components::general::{section_header, section_sub_header};
use crate::guinea::crash_prevention::to_proper_error;
use crate::guinea::Guineacorn;
use crate::unicorn::bitblasting::bitblast_model;
use crate::unicorn::bitblasting_dimacs::write_dimacs_model;
use crate::unicorn::bitblasting_printer::write_btor2_model;
use crate::unicorn::btor2file_parser::parse_btor2_string;
use crate::unicorn::optimize::{optimize_model_with_input, optimize_model_with_solver};
#[cfg(feature = "boolector")]
use crate::unicorn::smt_solver::boolector_impl;
use crate::unicorn::smt_solver::none_impl;
#[cfg(feature = "z3")]
use crate::unicorn::smt_solver::z3solver_impl;
use crate::unicorn::unroller::{prune_model, renumber_model, unroll_model};
use crate::unicorn::{write_model, Model};

pub(crate) fn input_window(data: &mut Guineacorn, ui: &mut Ui) {
    section_header(ui, "Input");

    section_sub_header(ui, "Selecting Input");
    input_selection(ui, data);

    section_sub_header(ui, "Model Creation");
    ui.add_enabled_ui(data.picked_path.is_some(), |ui| {
        model_creation(ui, data);
    });

    section_sub_header(ui, "Model modification");
    ui.add_enabled_ui(data.model.is_some(), |ui| {
        model_modification(ui, data);
    });

    section_sub_header(ui, "Output Handling");
    ui.add_enabled_ui(data.cli2gui.output.is_some(), |ui| {
        output_handling(ui, data);
    });
}

pub(crate) fn output_window(data: &mut Guineacorn, ui: &mut Ui) {
    section_header(ui, "Output");

    if is_concurrent(data) {
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
                match &data.cli2gui.output {
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

fn input_selection(ui: &mut Ui, data: &mut Guineacorn) {
    general::open_file(ui, data);

    if data.picked_path.is_none() {
        return;
    }

    general::load(ui, data, "Preview File", |data| {
        if let Some(program) = &data.program {
            match Disassembly::from(program) {
                Ok(disassembly) => {
                    data.cli2gui.output = Some(disassembly.to_string());
                }
                Err(e) => data.error = Some(Error::from(e)),
            }
        } else if let Some(model) = &data.model {
            data.cli2gui.output = Some(stringify_model(model));
        }

        data.program = None;
        data.model = None;
    });
}

fn model_creation(ui: &mut Ui, data: &mut Guineacorn) {
    ui.add_enabled_ui(data.model.is_none(), |ui| {
        ui.horizontal_wrapped(|ui| {
            ui.label("Number of machine-words usable as heap.");
            ui.add(egui::DragValue::new(&mut data.cli2gui.memory_data.max_heap));
        });
        ui.horizontal_wrapped(|ui| {
            ui.label("Number of machine-words usable as stack.");
            ui.add(egui::DragValue::new(
                &mut data.cli2gui.memory_data.max_stack,
            ));
        });
        ui.horizontal_wrapped(|ui| {
            ui.label("Total size of memory in MiB.");
            ui.add(
                egui::DragValue::new(&mut data.cli2gui.memory_data.memory_size)
                    .clamp_range(1..=1024),
            );
        });

        general::load(ui, data, "Create Model", |data| {
            data.cli2gui.output = Some(stringify_model(data.model.as_ref().unwrap()));
        });
    });
}

fn model_modification(ui: &mut Ui, data: &mut Guineacorn) {
    ui.add_enabled_ui(!(data.cli2gui.pruned || data.cli2gui.bit_blasted), |ui| {
        unroll(ui, data);
        prune(ui, data);
    });

    ui.add_enabled_ui(!data.cli2gui.bit_blasted, |ui| {
        bitblast(ui, data);
    });
}

fn output_handling(ui: &mut Ui, data: &mut Guineacorn) {
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
                fs::write(save_file, data.cli2gui.output.as_ref().unwrap()).ok();
            }
        }

        if ui.button("Reset Model").clicked() {
            data.reset_cli2gui();
        }
    });
}

fn stringify_model(model: &Model) -> String {
    let mut buf = BufWriter::new(Vec::new());
    let _ = write_model(model, &mut buf);
    let bytes = buf.into_inner().unwrap();
    String::from_utf8(bytes).unwrap()
}

fn bitblast(ui: &mut Ui, data: &mut Guineacorn) {
    ui.horizontal_wrapped(|ui| {
        if ui.button("Bit Blast").clicked() {
            let mut buf = BufWriter::new(Vec::new());

            data.cli2gui.bit_blasted = true;
            let bit_model = bitblast_model(data.model.as_ref().unwrap(), true, 64);
            let _ = if data.cli2gui.dimacs {
                write_dimacs_model(&bit_model, &mut buf)
            } else {
                write_btor2_model(&bit_model, &mut buf)
            };
            let bytes = buf.into_inner().unwrap();
            data.cli2gui.output = Some(String::from_utf8(bytes).unwrap());
        }
        ui.checkbox(&mut data.cli2gui.dimacs, "Output dimacs gate model");
    });
}

fn prune(ui: &mut Ui, data: &mut Guineacorn) {
    if ui.button("Prune Sequential Part").clicked() {
        data.cli2gui.pruned = true;
        prune_model(data.model.as_mut().unwrap());

        match data.cli2gui.solver {
            SmtType::Generic => optimize_model_with_solver::<none_impl::NoneSolver>(
                data.model.as_mut().unwrap(),
                data.cli2gui.timeout,
                data.cli2gui.minimize,
                false,
                false,
                false
            ),
            #[cfg(feature = "boolector")]
            SmtType::Boolector => optimize_model_with_solver::<boolector_impl::BoolectorSolver>(
                data.model.as_mut().unwrap(),
                data.cli2gui.timeout,
                data.cli2gui.minimize,
                false,
                false,
                false
            ),
            #[cfg(feature = "z3")]
            SmtType::Z3 => optimize_model_with_solver::<z3solver_impl::Z3SolverWrapper>(
                data.model.as_mut().unwrap(),
                data.cli2gui.timeout,
                data.cli2gui.minimize,
                false,
                false,
                false
            ),
        }
        renumber_model(data.model.as_mut().unwrap());
        data.cli2gui.output = Some(stringify_model(data.model.as_ref().unwrap()));
    }
}

fn unroll(ui: &mut Ui, data: &mut Guineacorn) {
    ui.horizontal_wrapped(|ui| {
        ui.label("Number of unrolls:");
        ui.add(egui::DragValue::new(&mut data.cli2gui.desired_unrolls));
        if ui.button("Do Unrolls").clicked() {
            do_unroll(data);
        }
        ui.label(format!("({} done so far)", data.cli2gui.times_unrolled));
    });

    ui.label("Optimizer:");
    ui.horizontal_wrapped(|ui| {
        ui.selectable_value(&mut data.cli2gui.solver, SmtType::Generic, "Generic");
        #[cfg(feature = "boolector")]
        ui.selectable_value(&mut data.cli2gui.solver, SmtType::Boolector, "Boolector");
        #[cfg(feature = "z3")]
        ui.selectable_value(&mut data.cli2gui.solver, SmtType::Z3, "Z3");
    });
    ui.label("Concrete inputs passed to optimizer:");
    ui.text_edit_singleline(&mut data.cli2gui.extras);
}

fn do_unroll(data: &mut Guineacorn) {
    data.loading_data.maximum = data.cli2gui.desired_unrolls as f32;
    data.loading_data.message = "Unrolling Model".to_string();

    let serial_model = stringify_model(data.model.as_ref().unwrap());
    let parameters = data.cli2gui.clone();

    data.cli2gui.times_unrolled += data.cli2gui.desired_unrolls;
    data.cli2gui.desired_unrolls = 0;
    data.cli2gui.output = None;
    data.model = None;

    let (sender, receiver): (Sender<f32>, Receiver<f32>) = std::sync::mpsc::channel();
    data.loading_data.progress_receiver = Some(receiver);

    let concurrent_unrolling = move || {
        let mut model = parse_btor2_string(&serial_model, &parameters.memory_data);
        model.lines.clear();

        for n in 0..parameters.desired_unrolls {
            unroll_model(&mut model, n);
            if !parameters.extras.is_empty() {
                optimize_model_with_input(
                    &mut model,
                    &mut parameters
                        .extras
                        .split(' ')
                        .map(|x| x.parse().unwrap_or(0))
                        .collect(),
                )
            }
            sender.send(n as f32).expect("Could not send progress.");
        }

        match parameters.solver {
            SmtType::Generic => optimize_model_with_solver::<none_impl::NoneSolver>(
                &mut model,
                parameters.timeout,
                parameters.minimize,
                false,
                false,
                false
            ),
            #[cfg(feature = "boolector")]
            SmtType::Boolector => optimize_model_with_solver::<boolector_impl::BoolectorSolver>(
                &mut model,
                parameters.timeout,
                parameters.minimize,
                false,
                false,
                false
            ),
            #[cfg(feature = "z3")]
            SmtType::Z3 => optimize_model_with_solver::<z3solver_impl::Z3SolverWrapper>(
                &mut model,
                parameters.timeout,
                parameters.minimize,
                false,
                false,
                false
            ),
        }

        renumber_model(&mut model);
        stringify_model(&model)
    };

    let processing_thread = thread::Builder::new()
        .stack_size(64 * 1024 * 1024) // increase thread stack size to avoid stack overflow
        .spawn(concurrent_unrolling);

    match processing_thread {
        Ok(thread) => data.loading_data.processing_thread = Some(thread),
        Err(e) => data.error = Some(Error::from(e)),
    }
}

fn is_concurrent(data: &mut Guineacorn) -> bool {
    match &data.loading_data.processing_thread {
        None => false,
        Some(thread) => {
            if !thread.is_finished() {
                return true;
            }
            let thread = data.loading_data.processing_thread.take().unwrap();
            let serial_model = thread.join();
            match serial_model {
                Ok(model) => {
                    let mut model = parse_btor2_string(&model, &data.cli2gui.memory_data);
                    renumber_model(&mut model);

                    data.model = Some(model);
                    data.cli2gui.output = Some(stringify_model(data.model.as_ref().unwrap()));
                }
                Err(e) => data.error = Some(to_proper_error(&e)),
            }
            false
        }
    }
}

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::Value::{Bitvector, Boolean};
use crate::guinea::giraphe::{Giraphe, Value};
use crate::guinea::Guineacorn;
use crate::unicorn::builder::generate_model;
use crate::unicorn::unroller::renumber_model;
use crate::unicorn::Node;
use bytesize::ByteSize;
use egui::{RichText, Ui};
use riscu::load_object_file;
use std::collections::HashMap;
use std::path::PathBuf;
use std::str::FromStr;

// TODO: Bad is true -> display
pub fn input_window(data: &mut Guineacorn, ui: &mut Ui) {
    ui.horizontal_wrapped(|ui| {
        ui.label("Select a BTOR2 file to start.");
        if ui.button("Open file...").clicked() {
            data.reset_model_params();
            if let Some(path) = rfd::FileDialog::new().pick_file() {
                data.picked_path = Some(path.display().to_string());
            }
        }
    });

    let picked_path = data
        .picked_path
        .clone()
        .unwrap_or_else(|| "NONE".to_string());

    ui.add_space(10.0);
    ui.add_enabled_ui(data.picked_path.is_some(), |ui| {
        ui.label("Selected File:");
        ui.monospace(&picked_path);

        if ui.button("Load Binary").clicked() {
            let path = PathBuf::from_str(&picked_path).unwrap();
            let program = load_object_file(path);

            let program = program.unwrap();
            let argv = [vec![picked_path.clone()]].concat();
            let mut model =
                generate_model(&program, ByteSize::mib(1).as_u64(), 8, 32, &argv).unwrap();
            renumber_model(&mut model);

            data.giraphe = Giraphe::from(&model);
        }

        ui.add_enabled_ui(!data.giraphe.leaves.is_empty(), |ui| {
            ui.horizontal(|ui| {
                if ui.button("Step Over").clicked() {
                    data.giraphe.tick_over();
                }
                ui.label(format!("Tick {}", data.giraphe.tick))
            });
        });

        ui.add_space(15.0);
        ui.separator();
        ui.heading("System State");
        ui.separator();
        ui.add_space(15.0);
        ui.heading("Registers");
        let regs = data
            .giraphe
            .registers
            .as_ref()
            .iter()
            .map(|x| {
                if let Some(x) = x {
                    let s = data.giraphe.nid_to_spot(x);
                    s.val_cur.clone()
                } else {
                    Bitvector(Concrete(0))
                }
            })
            .collect::<Vec<Value>>();

        ui.horizontal_top(|ui| {
            egui::Grid::new("registers1")
                .striped(true)
                .min_col_width(50.0)
                .max_col_width(50.0)
                .show(ui, |ui| {
                    ui.label("zero");
                    ui.label(format!("{}", regs.get(0).unwrap()));
                    ui.end_row();
                    ui.label("ra");
                    ui.label(format!("{}", regs.get(1).unwrap()));
                    ui.end_row();
                    ui.label("sp");
                    ui.label(format!("{}", regs.get(2).unwrap()));
                    ui.end_row();
                    ui.label("gp");
                    ui.label(format!("{}", regs.get(3).unwrap()));
                    ui.end_row();
                    ui.label("tp");
                    ui.label(format!("{}", regs.get(4).unwrap()));
                    ui.end_row();
                    ui.label("t0");
                    ui.label(format!("{}", regs.get(5).unwrap()));
                    ui.end_row();
                    ui.label("t1");
                    ui.label(format!("{}", regs.get(6).unwrap()));
                    ui.end_row();
                    ui.label("t2");
                    ui.label(format!("{}", regs.get(7).unwrap()));
                });
            egui::Grid::new("registers2")
                .striped(true)
                .min_col_width(50.0)
                .max_col_width(50.0)
                .show(ui, |ui| {
                    ui.label("s0");
                    ui.label(format!("{}", regs.get(8).unwrap()));
                    ui.end_row();
                    ui.label("s1");
                    ui.label(format!("{}", regs.get(9).unwrap()));
                    ui.end_row();
                    ui.label("a0");
                    ui.label(format!("{}", regs.get(10).unwrap()));
                    ui.end_row();
                    ui.label("a1");
                    ui.label(format!("{}", regs.get(11).unwrap()));
                    ui.end_row();
                    ui.label("a2");
                    ui.label(format!("{}", regs.get(12).unwrap()));
                    ui.end_row();
                    ui.label("a3");
                    ui.label(format!("{}", regs.get(13).unwrap()));
                    ui.end_row();
                    ui.label("a4");
                    ui.label(format!("{}", regs.get(14).unwrap()));
                    ui.end_row();
                    ui.label("a5");
                    ui.label(format!("{}", regs.get(15).unwrap()));
                    ui.end_row();
                });
            egui::Grid::new("registers3")
                .striped(true)
                .min_col_width(50.0)
                .max_col_width(50.0)
                .show(ui, |ui| {
                    ui.label("a6");
                    ui.label(format!("{}", regs.get(16).unwrap()));
                    ui.end_row();
                    ui.label("a7");
                    ui.label(format!("{}", regs.get(17).unwrap()));
                    ui.end_row();
                    ui.label("s2");
                    ui.label(format!("{}", regs.get(18).unwrap()));
                    ui.end_row();
                    ui.label("s3");
                    ui.label(format!("{}", regs.get(19).unwrap()));
                    ui.end_row();
                    ui.label("s4");
                    ui.label(format!("{}", regs.get(20).unwrap()));
                    ui.end_row();
                    ui.label("s5");
                    ui.label(format!("{}", regs.get(21).unwrap()));
                    ui.end_row();
                    ui.label("s6");
                    ui.label(format!("{}", regs.get(22).unwrap()));
                    ui.end_row();
                    ui.label("s7");
                    ui.label(format!("{}", regs.get(23).unwrap()));
                    ui.end_row();
                });
            egui::Grid::new("registers4")
                .striped(true)
                .min_col_width(50.0)
                .max_col_width(50.0)
                .show(ui, |ui| {
                    ui.label("s8");
                    ui.label(format!("{}", regs.get(24).unwrap()));
                    ui.end_row();
                    ui.label("s9");
                    ui.label(format!("{}", regs.get(25).unwrap()));
                    ui.end_row();
                    ui.label("s10");
                    ui.label(format!("{}", regs.get(26).unwrap()));
                    ui.end_row();
                    ui.label("s11");
                    ui.label(format!("{}", regs.get(27).unwrap()));
                    ui.end_row();
                    ui.label("t3");
                    ui.label(format!("{}", regs.get(28).unwrap()));
                    ui.end_row();
                    ui.label("t4");
                    ui.label(format!("{}", regs.get(29).unwrap()));
                    ui.end_row();
                    ui.label("t5");
                    ui.label(format!("{}", regs.get(30).unwrap()));
                    ui.end_row();
                    ui.label("t6");
                    ui.label(format!("{}", regs.get(31).unwrap()));
                    ui.end_row();
                });
        });
    });

    // pc and virtual memory
    let mut pc = None;
    let mut vm = HashMap::new();
    let mut kernel_mode = false;

    for x in &data.giraphe.states {
        let s = data.giraphe.nid_to_spot(x);
        match &*s.origin.borrow() {
            Node::State { name, .. } => {
                let name = name.as_ref().unwrap().as_str();
                if name == "virtual-memory" {
                    if let Value::Array(hm) = &s.val_cur {
                        vm = hm.clone();
                    }
                }

                if name.starts_with("pc=") && s.val_cur == Boolean(true) {
                    if pc.is_some() {
                        panic!("Multiple PCs active at once: {:?} and {:?}", pc, x);
                    }
                    pc = Some(String::from(&name[3..]));
                }

                if name.starts_with("kernel") {
                    kernel_mode |= Boolean(true) == s.val_cur;
                }
            }
            _ => unreachable!(),
        };
    }

    ui.add_space(15.0);
    ui.heading("Program Counter");
    ui.horizontal(|ui| {
        ui.label("PC =");
        ui.label(pc.unwrap_or_else(|| "Undefined".to_string()));
        if kernel_mode {
            ui.label("(kernel-mode is active)");
        }
    });

    ui.add_space(15.0);
    ui.heading("Virtual Memory");
    let mut vm: Vec<_> = vm.iter().collect();
    vm.sort_by(|(x, _), (y, _)| {
        let Concrete(x) = x;
        let Concrete(y) = y;
        x.cmp(y)
    });

    // TODO: differentiate stack, heap and data segment
    egui::ScrollArea::vertical()
        .auto_shrink([false; 2])
        .show(ui, |ui| {
            egui::Grid::new("virtual memory").show(ui, |ui| {
                for (k, v) in vm {
                    let Concrete(k) = k;
                    let Concrete(v) = v;
                    ui.label(RichText::new(format!("0x{:08x}", k)).monospace());
                    ui.label(format!("{}", v));
                    ui.end_row();
                }
            });
        });
}

pub fn output_window(data: &mut Guineacorn, ui: &mut Ui) {
    data.giraphe.draw(ui);
    data.giraphe.interact(ui);
}

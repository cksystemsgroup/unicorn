use std::iter::zip;

use anyhow::Error;
use egui::{RichText, Ui};
use indexmap::IndexMap;
use riscu::{decode, Register};

use unicorn::disassemble::Disassembly;

use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::{Giraphe, MachineWord, Value};
use crate::guinea::Guineacorn;

pub(crate) fn step(ui: &mut Ui, graph: &mut Giraphe) {
    ui.add_enabled_ui(!graph.in_bad_state, |ui| {
        ui.horizontal(|ui| {
            if ui.button("Step Over").clicked() {
                graph.tick_over();
            }
            if ui.button("Step until input").clicked() {
                while !(graph.in_bad_state
                    || graph.a7_is_read_or_exit() && graph.is_in_kernel_mode())
                {
                    graph.tick_over();
                }
            }
            ui.label(format!("Tick {}", graph.tick))
        })
    });
}

pub(crate) fn input(ui: &mut Ui, graph: &mut Giraphe) {
    ui.horizontal(|ui| {
        if graph.is_ascii {
            let edit =
                egui::TextEdit::singleline(&mut graph.input_ascii).hint_text("Character Buffer");
            ui.add(edit)
                .on_hover_text("Missing buffer item defaults to zero");
        } else {
            let nr = egui::DragValue::new(&mut graph.input_number);
            ui.add(nr);
            ui.label("(limited to max 2^8-1=255)");
        }
        ui.checkbox(&mut graph.is_ascii, "Interpret as ASCII");
    });
    egui::ScrollArea::vertical()
        .max_height(30.0)
        .auto_shrink([false, true])
        .show(ui, |ui| {
            for (i, s) in zip(1.., &graph.consumed_inputs) {
                ui.label(format!("Input {i}: {s}"));
            }
        });
}

pub(crate) fn registers(ui: &mut Ui, regs: Vec<Value>) {
    ui.heading("Registers");
    ui.horizontal_top(|ui| {
        for col in 0..4 {
            egui::Grid::new(format!("registers{col}"))
                .striped(true)
                .min_col_width(30.0)
                .max_col_width(50.0)
                .show(ui, |ui| {
                    for i in 0..8 {
                        let idx = i + 8 * col;
                        let register = Register::from(idx);
                        ui.label(format!("{:?}", register));
                        ui.label(format!("{}", regs.get(idx as usize).unwrap()));
                        ui.end_row();
                    }
                });
        }
    });
}

pub(crate) fn program_counter(
    ui: &mut Ui,
    pc: Option<u64>,
    kernel_mode: bool,
    data: &mut Guineacorn,
) {
    ui.heading("Program Counter");
    ui.horizontal(|ui| {
        ui.monospace(if let Some(pc) = pc {
            format!("PC = 0x{:08x}", pc)
        } else {
            "PC = Undefined".to_string()
        });

        if kernel_mode {
            let sys_id = data
                .giraphe
                .nid_to_spot(&data.giraphe.registers[17].unwrap())
                .current_value
                .clone();
            ui.label(format!("(kernel-mode is active, syscall: {})", sys_id));
        }

        if let Some(pc) = pc {
            let pc = pc - data.program.as_ref().unwrap().code.address;
            let pc = pc / 4;
            let inst = &data.program.as_ref().unwrap().code.content;
            let chunks = inst.chunks(4).collect::<Vec<_>>();
            let inst = chunks.get(pc as usize).unwrap();
            let inst = ((inst[3] as u32) << 24)
                + ((inst[2] as u32) << 16)
                + ((inst[1] as u32) << 8)
                + inst[0] as u32;
            let inst = decode(inst).unwrap();
            let inst = format!("corresponds to {:?}", inst);
            ui.monospace(inst);
        };
    });
    ui.collapsing("Full Program", |ui| {
        match Disassembly::from(data.program.as_ref().unwrap()) {
            Ok(disassembly) => {
                ui.monospace(disassembly.to_string());
            }
            Err(e) => data.error = Some(Error::from(e)),
        }
    });
}

pub(crate) fn virtual_memory(ui: &mut Ui, vm: IndexMap<MachineWord, MachineWord>) {
    ui.heading("Virtual Memory");
    let mut vm: Vec<_> = vm.iter().collect();
    vm.sort_by(|(x, _), (y, _)| {
        let Concrete(x) = x;
        let Concrete(y) = y;
        x.cmp(y)
    });

    egui::ScrollArea::vertical()
        .id_source("virtual memory scroll")
        .auto_shrink([false, true])
        .show(ui, |ui| {
            egui::Grid::new("virtual memory grid").show(ui, |ui| {
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

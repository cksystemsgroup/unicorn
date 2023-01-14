use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::{Giraphe, MachineWord, Value};
use crate::guinea::print::stringify_program;
use crate::guinea::Guineacorn;
use egui::{RichText, Ui};
use indexmap::IndexMap;
use riscu::decode;
use std::iter::zip;

pub fn step(ui: &mut Ui, graph: &mut Giraphe) {
    ui.horizontal(|ui| {
        if ui.button("Step Over").clicked() {
            graph.tick_over();
        }
        if ui.button("Step until input").clicked() {
            while !(graph.a7_is_read_or_exit() && graph.is_in_kernel_mode()) {
                graph.tick_over();
            }
        }
        ui.label(format!("Tick {}", graph.tick))
    });
}

pub fn input(ui: &mut Ui, graph: &mut Giraphe) {
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
            for (i, s) in zip(1.., &graph.input_queue) {
                ui.label(format!("Input {i}: {s}"));
            }
        });
}

pub fn registers(ui: &mut Ui, regs: Vec<Value>) {
    ui.heading("Registers");

    // TODO: get rid of magic numbers when selecting registers
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
}

pub fn program_counter(ui: &mut Ui, pc: u64, kernel_mode: bool, data: &Guineacorn) {
    ui.heading("Program Counter");
    ui.horizontal(|ui| {
        ui.monospace(if pc != 0 {
            format!("PC = 0x{:08x}", pc)
        } else {
            "PC = Undefined".to_string()
        });
        if kernel_mode {
            let sys_id = data
                .giraphe
                .nid_to_spot(&data.giraphe.registers[17].unwrap())
                .val_cur
                .clone();
            ui.label(format!("(kernel-mode is active, syscall: {})", sys_id));
        }
        if pc != 0 {
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
        ui.label(stringify_program(data.program.as_ref().unwrap()));
    });
}

pub fn virtual_memory(ui: &mut Ui, vm: IndexMap<MachineWord, MachineWord>) {
    ui.heading("Virtual Memory");
    let mut vm: Vec<_> = vm.iter().collect();
    vm.sort_by(|(x, _), (y, _)| {
        let Concrete(x) = x;
        let Concrete(y) = y;
        x.cmp(y)
    });

    // TODO: differentiate stack, heap and data segment
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

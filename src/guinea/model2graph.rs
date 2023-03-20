use crate::guinea::components::general::section_sub_header;
use crate::guinea::components::{general, machine};
use egui::Ui;

use crate::guinea::giraphe::Giraphe;
use crate::guinea::Guineacorn;

pub(crate) fn input_window(data: &mut Guineacorn, ui: &mut Ui) {
    section_sub_header(ui, "Model Creation");
    general::open_file(ui, data);
    ui.add_space(10.0);

    ui.add_enabled_ui(data.picked_path.is_some(), |ui| {
        general::load(ui, data, "Load File", |data: &mut Guineacorn| {
            data.giraphe = Giraphe::from(data.model.as_ref().unwrap());
        });
    });
    ui.add_space(15.0);

    if data.model.is_none() {
        return;
    }

    egui::ScrollArea::vertical()
        .auto_shrink([false, true])
        .show(ui, |ui| {
            section_sub_header(ui, "Navigation");
            machine::step(ui, &mut data.giraphe);
            ui.add_space(10.0);
            machine::input(ui, &mut data.giraphe);
            ui.add_space(15.0);

            if data.program.is_none() {
                return;
            }

            section_sub_header(ui, "Machine State");
            let (regs, pc, kernel_mode, vm) = data.giraphe.system_state();
            machine::registers(ui, regs);
            ui.add_space(15.0);
            machine::program_counter(ui, pc, kernel_mode, data);
            ui.add_space(15.0);
            machine::virtual_memory(ui, vm);
        });
}

pub(crate) fn output_window(data: &mut Guineacorn, ui: &mut Ui) {
    data.giraphe.draw(ui);
    data.giraphe.interact(ui);
}

use crate::guinea::components::{general, machine};
use egui::Ui;

use crate::guinea::giraphe::Giraphe;
use crate::guinea::Guineacorn;

// TODO: display if bad state became true
pub fn input_window(data: &mut Guineacorn, ui: &mut Ui) {
    ui.separator();
    ui.heading("Model Creation");
    ui.separator();
    general::open_file(ui, data);

    ui.add_space(10.0);
    ui.add_enabled_ui(data.picked_path.is_some(), |ui| {
        general::load_binary(ui, data, |data: &mut Guineacorn| {
            data.giraphe = Giraphe::from(data.model.as_ref().unwrap());
        });
    });

    if data.model.is_none() {
        return;
    }
    ui.add_space(15.0);

    // Machine
    ui.separator();
    ui.heading("Navigation");
    ui.separator();
    machine::step(ui, &mut data.giraphe);
    ui.add_space(10.0);
    machine::input(ui, &mut data.giraphe);
    ui.add_space(15.0);

    ui.separator();
    ui.heading("System State");
    ui.separator();
    let (regs, pc, kernel_mode, vm) = data.giraphe.system_state();
    machine::registers(ui, regs);
    ui.add_space(15.0);
    machine::program_counter(ui, pc, kernel_mode, &data.giraphe);
    ui.add_space(15.0);
    machine::virtual_memory(ui, vm);
}

pub fn output_window(data: &mut Guineacorn, ui: &mut Ui) {
    data.giraphe.draw(ui);
    data.giraphe.interact(ui);
}

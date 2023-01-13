use crate::guinea::Guineacorn;
use crate::unicorn::btor2file_parser::parse_btor2_file;
use crate::unicorn::builder::generate_model;
use crate::unicorn::unroller::renumber_model;
use bytesize::ByteSize;
use egui::Ui;
use riscu::load_object_file;
use std::path::PathBuf;
use std::str::FromStr;

pub fn open_file(ui: &mut Ui, data: &mut Guineacorn) {
    ui.horizontal_wrapped(|ui| {
        ui.label("Select a file to start.");
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
    ui.label("Selected File:");
    ui.monospace(&picked_path);
}

pub fn load_binary(ui: &mut Ui, data: &mut Guineacorn, after_fn: fn(&mut Guineacorn)) {
    if ui.button("Load Binary").clicked() {
        let picked_path = data.picked_path.as_ref().unwrap();
        let path = PathBuf::from_str(picked_path).unwrap();
        data.program = load_object_file(path).ok();
        let argv = [vec![picked_path.clone()]].concat();
        let mut model = generate_model(
            data.program.as_ref().unwrap(),
            ByteSize::mib(1).as_u64(),
            8,
            32,
            &argv,
        )
        .unwrap();
        renumber_model(&mut model);
        data.model = Some(model);
        after_fn(data);
    }
}

pub fn load_model(ui: &mut Ui, data: &mut Guineacorn, after_fn: fn(&mut Guineacorn)) {
    if ui.button("Load Model").clicked() {
        let picked_path = data.picked_path.as_ref().unwrap();
        let path = PathBuf::from_str(picked_path).unwrap();
        let mut model = parse_btor2_file(&path);
        renumber_model(&mut model);
        data.model = Some(model);
        after_fn(data);
    }
}

use crate::guinea::crash_prevention::try_catch;
use crate::guinea::Guineacorn;
use crate::unicorn::btor2file_parser::parse_btor2_file;
use crate::unicorn::builder::generate_model;
use crate::unicorn::unroller::renumber_model;
use anyhow::Error;
use bytesize::ByteSize;
use egui::Ui;
use riscu::load_object_file;
use std::path::PathBuf;
use std::str::FromStr;

pub(crate) fn open_file(ui: &mut Ui, data: &mut Guineacorn) {
    ui.horizontal_wrapped(|ui| {
        ui.label("Select a file to start.");
        if ui.button("Open file...").clicked() {
            data.reset_cli2gui();
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

pub(crate) fn load(
    ui: &mut Ui,
    data: &mut Guineacorn,
    button_text: &str,
    after_fn: fn(&mut Guineacorn),
) {
    if ui.button(button_text).clicked() {
        let picked_path = data.picked_path.as_ref().unwrap();
        let path = PathBuf::from_str(picked_path).unwrap();

        if let Ok(program) = load_object_file(&path) {
            data.program = Some(program);
            let argv = [vec![picked_path.clone()]].concat();
            let mut model = generate_model(
                data.program.as_ref().unwrap(),
                ByteSize::mib(1).as_u64(),
                8,
                32,
                false,
                &argv,
            )
            .unwrap();
            renumber_model(&mut model);
            data.model = Some(model);

            after_fn(data);
            return;
        }

        if let Ok(mut model) = try_catch(|| parse_btor2_file(&path)) {
            renumber_model(&mut model);
            data.model = Some(model);
            after_fn(data);
            return;
        }

        data.error = Some(Error::msg("File is neither a binary nor a model"));
    }
}

pub(crate) fn section_header(ui: &mut Ui, title: &str) {
    ui.heading(title);
    ui.separator();
    ui.separator();
    ui.add_space(10.0);
}

pub(crate) fn section_sub_header(ui: &mut Ui, title: &str) {
    ui.label(title);
    ui.separator();
    ui.add_space(5.0);
}

use crate::guinea::giraphe::Giraphe;
use crate::guinea::Guineacorn;
use crate::unicorn::btor2file_parser::parse_btor2_file;
use crate::unicorn::unroller::renumber_model;
use crate::unicorn::Node;
use egui::Ui;
use std::path::PathBuf;
use std::str::FromStr;

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

        if ui.button("Load File").clicked() {
            data.reset_model_params();
            // TODO: do proper input validation
            let path = PathBuf::from_str(&picked_path).unwrap();
            let mut model = parse_btor2_file(&path);
            renumber_model(&mut model);
            data.giraphe = Giraphe::from(&model);
        }

        ui.add_enabled_ui(!data.giraphe.leaves.is_empty(), |ui| {
            if ui.button("Step Over").clicked() {
                let t = data.giraphe.tick_over();
                println!("Tick: {t}");
            }
        });

        ui.label("Leaf values");
        egui::ScrollArea::vertical().show(ui, |ui| {
            for sr in &data.giraphe.leaves {
                let l = &*sr.borrow();
                let text = match &*l.origin.borrow() {
                    Node::Bad { name, .. } => {
                        format!("Bad ({}): {}", name.as_ref().unwrap(), l.val_cur)
                    }
                    Node::Next { state, .. } => match &*state.borrow() {
                        Node::State { name, .. } => {
                            format!("Next ({}): {}", name.as_ref().unwrap(), l.val_cur)
                        }
                        _ => unreachable!(),
                    },
                    x => unreachable!("{:?}", x),
                };
                ui.label(text);
            }
        });
    });
}

pub fn output_window(data: &mut Guineacorn, ui: &mut Ui) {
    data.giraphe.draw(ui);
    data.giraphe.interact(ui);
}

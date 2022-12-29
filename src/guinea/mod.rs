use riscu::Program;
use std::sync::mpsc::Receiver;

use crate::guinea::cli2gui::Cli2Gui;
use crate::guinea::giraphe::Giraphe;
use crate::unicorn::Model;

mod cli2gui;
mod components;
mod design;
mod error_handling;
mod giraphe;
pub mod gui;
mod model2graph;
mod print;

#[derive(Clone)]
pub struct MemoryData {
    pub memory_size: u64,
    pub max_heap: u32,
    pub max_stack: u32,
    pub data_start: u64,
    pub data_end: u64,
}

impl Default for MemoryData {
    fn default() -> Self {
        Self {
            memory_size: 1,
            data_start: 0,
            data_end: 0,
            max_heap: 8,
            max_stack: 32,
        }
    }
}

#[derive(Default)]
pub struct Guineacorn {
    pub model: Option<Model>,
    pub program: Option<Program>,
    pub picked_path: Option<String>,
    pub output: Option<String>,
    pub model_created: bool,
    pub using: Use,

    pub error_message: Option<String>,
    pub error_occurred: bool,

    pub memory_data: MemoryData,
    pub loading_data: LoadingData,
    pub cli2gui: Cli2Gui,
    pub giraphe: Giraphe,
}

#[derive(Default)]
pub struct LoadingData {
    message: String,
    progress: f32,
    maximum: f32,
    progress_receiver: Option<Receiver<f32>>,
}

impl Guineacorn {
    pub fn reset_model_params(&mut self) {
        self.model_created = false;
        self.cli2gui.bit_blasted = false;
        self.cli2gui.pruned = false;
        self.cli2gui.times_unrolled = 0;
        self.cli2gui.unroller = None;
        self.model = None;
        self.output = None;
    }
}

#[derive(Default, PartialEq, Eq)]
pub enum Use {
    Cli2Gui,
    #[default]
    NodeGraph,
}

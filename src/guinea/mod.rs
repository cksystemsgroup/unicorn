use crate::cli::SmtType;
use riscu::Program;
use std::sync::mpsc::Receiver;
use std::thread::JoinHandle;
use std::time::Duration;

use crate::guinea::giraphe::Giraphe;
use crate::unicorn::Model;

mod cli2gui;
mod components;
mod crash_prevention;
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
    pub using: Use,

    pub error: Option<anyhow::Error>,

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
    processing_thread: Option<JoinHandle<String>>,
}

impl Guineacorn {
    pub fn reset_cli2gui(&mut self) {
        self.cli2gui.bit_blasted = false;
        self.cli2gui.pruned = false;
        self.cli2gui.times_unrolled = 0;
        self.cli2gui.output = None;
        self.model = None;
    }
}

#[derive(Clone)]
pub struct Cli2Gui {
    pub bit_blasted: bool,
    pub pruned: bool,
    pub from_beator: bool,
    pub extras: String,
    pub times_unrolled: usize,
    pub desired_unrolls: usize,
    pub dimacs: bool,
    pub solver: SmtType,
    pub minimize: bool,
    pub timeout: Option<Duration>,
    pub memory_data: MemoryData,
    pub output: Option<String>,
}

impl Default for Cli2Gui {
    fn default() -> Self {
        Self {
            bit_blasted: false,
            pruned: false,
            from_beator: false,
            extras: "".to_string(),
            times_unrolled: 0,
            desired_unrolls: 0,
            dimacs: false,
            solver: SmtType::Generic,
            minimize: false,
            timeout: None,
            memory_data: Default::default(),
            output: None,
        }
    }
}

#[derive(Default, PartialEq, Eq)]
pub enum Use {
    #[default]
    Cli2Gui,
    NodeGraph,
}

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
pub(crate) mod gui;
mod model2graph;

#[derive(Clone)]
pub struct MemoryData {
    pub(crate) memory_size: u64,
    pub(crate) max_heap: u32,
    pub(crate) max_stack: u32,
    pub(crate) data_start: u64,
    pub(crate) data_end: u64,
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
pub(crate) struct Guineacorn {
    pub(crate) model: Option<Model>,
    pub(crate) program: Option<Program>,
    pub(crate) picked_path: Option<String>,
    pub(crate) using: Use,

    pub(crate) error: Option<anyhow::Error>,

    pub(crate) loading_data: LoadingData,
    pub(crate) cli2gui: Cli2Gui,
    pub(crate) giraphe: Giraphe,
}

#[derive(Default)]
pub(crate) struct LoadingData {
    message: String,
    progress: f32,
    maximum: f32,
    progress_receiver: Option<Receiver<f32>>,
    processing_thread: Option<JoinHandle<String>>,
}

impl Guineacorn {
    pub(crate) fn reset_cli2gui(&mut self) {
        self.cli2gui.bit_blasted = false;
        self.cli2gui.pruned = false;
        self.cli2gui.times_unrolled = 0;
        self.cli2gui.output = None;
        self.model = None;
    }
}

#[derive(Clone)]
pub(crate) struct Cli2Gui {
    pub(crate) bit_blasted: bool,
    pub(crate) pruned: bool,
    pub(crate) extras: String,
    pub(crate) times_unrolled: usize,
    pub(crate) desired_unrolls: usize,
    pub(crate) dimacs: bool,
    pub(crate) solver: SmtType,
    pub(crate) minimize: bool,
    pub(crate) timeout: Option<Duration>,
    pub(crate) memory_data: MemoryData,
    pub(crate) output: Option<String>,
}

impl Default for Cli2Gui {
    fn default() -> Self {
        Self {
            bit_blasted: false,
            pruned: false,
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
pub(crate) enum Use {
    #[default]
    Cli2Gui,
    NodeGraph,
}

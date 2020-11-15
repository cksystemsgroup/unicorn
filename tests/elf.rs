mod common;

use common::{compile_all_riscu, init};
use monster::elf::*;
use rayon::prelude::*;

#[test]
fn can_load_riscu_elf_files() {
    init();

    compile_all_riscu().1.for_each(|(source, object)| {
        let program = load_file(object, 10);

        assert!(
            program.is_some(),
            "can load RISC-U object file of {}",
            source.to_str().unwrap()
        );
    });
}

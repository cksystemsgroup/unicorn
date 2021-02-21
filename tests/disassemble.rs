mod common;

use common::{compile_riscu, init, with_temp_dir};
use monster::disassemble::*;
use rayon::prelude::*;

#[test]
fn can_disassemble_risc_u_binary() {
    init();

    with_temp_dir(|dir| {
        compile_riscu(dir, None).for_each(|(source, object)| {
            let result = disassemble(object);

            assert!(
                result.is_ok(),
                "can disassemble object file of {}",
                source.to_str().unwrap()
            );
        });
    });
}

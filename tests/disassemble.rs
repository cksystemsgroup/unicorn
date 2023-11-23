use rayon::prelude::*;
use unicorn::disassemble::*;

mod utils;
use utils::{compile_riscu, init, with_temp_dir};

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

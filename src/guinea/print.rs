use crate::unicorn::{write_model, Model};
use riscu::{decode, Program};
use std::io::BufWriter;

pub fn stringify_program(program: &Program) -> String {
    let mut lines: Vec<String> = vec![format!("{} instructions:", program.code.content.len() / 4)];
    let mut inst_items: Vec<String> = program
        .code
        .content
        .chunks(4)
        .zip((program.code.address..).step_by(4))
        .map(|(c, i)| {
            let mut res: u32 = 0;
            for x in c.iter().rev() {
                res <<= 8;
                res += u32::from(*x);
            }

            let instruction = match decode(res) {
                Ok(x) => format!("{:?}", x),
                Err(_) => format!("{:032b} (could not decode)", res),
            };

            format!("0x{:x}: {}", i, instruction)
        })
        .collect();
    lines.append(&mut inst_items);

    lines.push(format!("\n{} data items:", program.data.content.len() / 8));
    let mut data_items: Vec<String> = program
        .data
        .content
        .chunks(8)
        .rev()
        .zip((program.data.address..).step_by(8))
        .map(|(c, i)| {
            let mut res: u64 = 0;
            for x in c.iter().rev() {
                res <<= 8;
                res += u64::from(*x);
            }
            format!("0x{:x}: 0x{:08x} ({})", i, res, res)
        })
        .collect();
    lines.append(&mut data_items);
    lines.join("\n")
}

pub fn stringify_model(model: &Model) -> String {
    let mut buf = BufWriter::new(Vec::new());
    let _ = write_model(model, &mut buf);
    let bytes = buf.into_inner().unwrap();
    String::from_utf8(bytes).unwrap()
}
use crate::unicorn::bitblasting::GateModel;
use crate::unicorn::get_nid;
use anyhow::Result;
use std::collections::HashMap;
use std::io::Write;

//
// Public Interface
//

pub fn write_openqasm_code<W>(gate_model: &GateModel, out: W) -> Result<()>
where
    W: Write,
{
    // let zip = gate_model
    //     .bad_state_nodes
    //     .iter()
    //     .zip(gate_model.bad_state_gates.iter());
    let mut printer = OpenQasmPrinter::new(out);
    printer.print_file_header()?;
    printer.print_input_initialization(gate_model)?;
    // for (bad_state, gate) in zip {
    //     printer.print_bad_state(bad_state, gate)?;
    // }
    // for (gate, val) in &gate_model.constraints {
    //     printer.print_constraint(&gate.value, *val)?;
    // }
    printer.print_input_measurement(gate_model)?;
    Ok(())
}

struct OpenQasmPrinter<W> {
    out: W,
    _ancilla_count: i32,
}

impl<W: Write> OpenQasmPrinter<W> {
    fn new(out: W) -> Self {
        Self {
            out,
            _ancilla_count: 0,
        }
    }

    fn print_file_header(&mut self) -> Result<()> {
        writeln!(self.out, "// cksystemsgroup.github.io/unicorn\n")?;
        writeln!(self.out, "OPENQASM 2.0\n")?;
        writeln!(self.out, "include \"qelib1.inc\"\n\n\n")?;
        Ok(())
    }

    fn print_input_initialization(&mut self, gate_model: &GateModel) -> Result<()> {
        writeln!(self.out, "//inputs declaration\n\n")?;
        let mut nid_counts: HashMap<u64, i32> = HashMap::new();

        for (node, gates) in &gate_model.input_gates {
            let nid = get_nid(node);

            nid_counts.entry(nid).or_insert(0);
            (*nid_counts.get_mut(&nid).unwrap()) += 1;

            let timestep: i32 = *nid_counts.get(&nid).unwrap();

            writeln!(self.out, "//input at nid {}, timestep {}\n", nid, timestep)?;
            writeln!(self.out, "qreg qin{}_{}[{}]\n", nid, timestep, gates.len())?;
            writeln!(
                self.out,
                "creg cin{}_{}[{}]\n\n",
                nid,
                timestep,
                gates.len()
            )?;
            writeln!(self.out, "//apply hadamard gate\n")?;
            writeln!(self.out, "h qin{}_{}\n", nid, timestep)?;
        }
        writeln!(self.out, "\n")?;
        Ok(())
    }

    fn print_input_measurement(&mut self, gate_model: &GateModel) -> Result<()> {
        writeln!(self.out, "//inputs measurement\n\n")?;
        let mut nid_counts: HashMap<u64, i32> = HashMap::new();

        for (node, _gates) in &gate_model.input_gates {
            let nid = get_nid(node);

            nid_counts.entry(nid).or_insert(0);

            (*nid_counts.get_mut(&nid).unwrap()) += 1;

            let timestep: i32 = *nid_counts.get(&nid).unwrap();

            writeln!(
                self.out,
                "//measure input qubits for nid {}, and timestep {}\n",
                nid, timestep
            )?;
            writeln!(
                self.out,
                "measure qin{}_{} -> cin{}_{}\n",
                nid, timestep, nid, timestep
            )?;
        }
        writeln!(self.out, "\n")?;

        Ok(())
    }
}

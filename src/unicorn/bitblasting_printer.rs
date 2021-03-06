use crate::unicorn::bitblasting::{Gate, GateModel, GateRef, HashableGateRef};
use crate::unicorn::{Nid, Node, NodeRef};
use anyhow::Result;
use std::collections::HashMap;
use std::io::Write;

//
// Public Interface
//

pub fn write_btor2_model<W>(gate_model: &GateModel, out: W) -> Result<()>
where
    W: Write,
{
    let zip = gate_model
        .bad_state_nodes
        .iter()
        .zip(gate_model.bad_state_gates.iter());
    let mut printer = GateModelPrinter::new(out);
    printer.print_file_header()?;
    for (bad_state, gate) in zip {
        printer.print_bad_state(bad_state, gate)?;
    }
    for (gate, val) in &gate_model.constraints {
        printer.print_constraint(&gate.value, *val)?;
    }
    printer.print_file_footer()?;
    Ok(())
}

//
// Private Implementation
//

struct GateModelPrinter<W> {
    current_nid: Nid,
    nid_mapping: HashMap<HashableGateRef, Nid>,
    out: W,
}

impl<W: Write> GateModelPrinter<W> {
    fn new(out: W) -> Self {
        Self {
            current_nid: 70000000,
            nid_mapping: HashMap::new(),
            out,
        }
    }

    fn next_nid(&mut self) -> Nid {
        let nid = self.current_nid;
        self.current_nid += 1;
        nid
    }

    fn visit(&mut self, gate: &GateRef) -> Nid {
        let key = HashableGateRef::from(gate.clone());
        self.nid_mapping.get(&key).copied().unwrap_or_else(|| {
            let assigned_nid = self.process(gate).expect("ok");
            assert!(!self.nid_mapping.contains_key(&key));
            self.nid_mapping.insert(key, assigned_nid);
            assigned_nid
        })
    }

    #[rustfmt::skip]
    fn process(&mut self, gate: &GateRef) -> Result<Nid> {
        match &*gate.borrow() {
            Gate::ConstTrue => {
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} constd 1 1", gate_nid)?;
                Ok(gate_nid)
            }
            Gate::ConstFalse => {
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} constd 1 0", gate_nid)?;
                Ok(gate_nid)
            }
            Gate::InputBit { name } => {
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} state 1 {}", gate_nid, name)?;
                Ok(gate_nid)
            }
            Gate::Not { value } => {
                let value_nid = self.visit(value);
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} not 1 {}", gate_nid, value_nid)?;
                Ok(gate_nid)
            }
            Gate::And { left, right } => {
                let left_nid = self.visit(left);
                let right_nid = self.visit(right);
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} and 1 {} {}", gate_nid, left_nid, right_nid)?;
                Ok(gate_nid)
            }
            Gate::Nand { left, right } => {
                let left_nid = self.visit(left);
                let right_nid = self.visit(right);
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} nand 1 {} {}", gate_nid, left_nid, right_nid)?;
                Ok(gate_nid)
            }
            Gate::Or { left, right } => {
                let left_nid = self.visit(left);
                let right_nid = self.visit(right);
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} or 1 {} {}", gate_nid, left_nid, right_nid)?;
                Ok(gate_nid)
            }
            Gate::Matriarch1 { cond, right } => {
                let cond_nid = self.visit(cond);
                let right_nid = self.visit(right);
                let inner_not_nid = self.next_nid();
                let gate_nid = self.next_nid();
                // Modeling as `M := and(not(A), B)` here:
                writeln!(self.out, "{} not 1 {}", inner_not_nid, cond_nid)?;
                writeln!(self.out, "{} and 1 {} {}", gate_nid, inner_not_nid, right_nid)?;
                Ok(gate_nid)
            }
            Gate::CarryHalfAdder { left, right } => {
                let left_nid = self.visit(left);
                let right_nid = self.visit(right);
                let gate_nid = self.next_nid();
                // Modeling as `C := and(A, B)` here:
                writeln!(self.out, "{} and 1 {} {}", gate_nid, left_nid, right_nid)?;
                Ok(gate_nid)
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let input1_nid = self.visit(input1);
                let input2_nid = self.visit(input2);
                let gate_nid = self.next_nid();
                // Modeling as `S := xor(A, B)` here:
                writeln!(self.out, "{} xor 1 {} {}", gate_nid, input1_nid, input2_nid)?;
                Ok(gate_nid)
            }
            Gate::CarryFullAdder { input1, input2, input3 } => {
                let input1_nid = self.visit(input1);
                let input2_nid = self.visit(input2);
                let input3_nid = self.visit(input3);
                let inner_xor_nid = self.next_nid();
                let inner_and1_nid = self.next_nid();
                let inner_and2_nid = self.next_nid();
                let gate_nid = self.next_nid();
                // Modeling as `C_out := or(and(xor(A, B), C_in), and(A, B))` here:
                writeln!(self.out, "{} xor 1 {} {}", inner_xor_nid, input1_nid, input2_nid)?;
                writeln!(self.out, "{} and 1 {} {}", inner_and1_nid, inner_xor_nid, input3_nid)?;
                writeln!(self.out, "{} and 1 {} {}", inner_and2_nid, input1_nid, input2_nid)?;
                writeln!(self.out, "{} or 1 {} {}", gate_nid, inner_and1_nid, inner_and2_nid)?;
                Ok(gate_nid)
            }
            Gate::ResultFullAdder { input1, input2, input3 } => {
                let input1_nid = self.visit(input1);
                let input2_nid = self.visit(input2);
                let input3_nid = self.visit(input3);
                let inner_xor_nid = self.next_nid();
                let gate_nid = self.next_nid();
                // Modeling as `S := xor(xor(A, B), C_in)` here:
                writeln!(self.out, "{} xor 1 {} {}", inner_xor_nid, input1_nid, input2_nid)?;
                writeln!(self.out, "{} xor 1 {} {}", gate_nid, inner_xor_nid, input3_nid)?;
                Ok(gate_nid)
            }
            Gate::Quotient { name, .. } | Gate::Remainder { name, .. } => {
                let gate_nid = self.next_nid();
                writeln!(self.out, "{} state 1 {}", gate_nid, name)?;
                Ok(gate_nid)
            }
        }
    }

    fn print_file_header(&mut self) -> Result<()> {
        writeln!(self.out, "; cksystemsgroup.github.io/unicorn\n")?;
        writeln!(self.out, "1 sort bitvec 1 ; Boolean")?;
        writeln!(self.out, "\n; Model has been bitblasted.\n")?;
        Ok(())
    }

    fn print_bad_state(&mut self, bad_state: &NodeRef, gate: &GateRef) -> Result<()> {
        let bad_condition_nid = self.visit(gate);
        if let Node::Bad { name, .. } = &*bad_state.borrow() {
            let bad_state_nid = self.next_nid();
            writeln!(
                self.out,
                "{} bad {} {}",
                bad_state_nid,
                bad_condition_nid,
                name.as_deref().unwrap_or("?")
            )?;
            Ok(())
        } else {
            panic!("expecting 'Bad' node here");
        }
    }

    fn print_constraint(&mut self, gate: &GateRef, val: bool) -> Result<()> {
        let gate_nid = self.visit(gate);
        if val {
            let constraint_nid = self.next_nid();
            writeln!(self.out, "{} constraint {}", constraint_nid, gate_nid)?;
        } else {
            let inverter_nid = self.next_nid();
            let constraint_nid = self.next_nid();
            writeln!(self.out, "{} not 1 {}", inverter_nid, gate_nid)?;
            writeln!(self.out, "{} constraint {}", constraint_nid, inverter_nid)?;
        }
        Ok(())
    }

    fn print_file_footer(&mut self) -> Result<()> {
        writeln!(self.out, "\n; end of BTOR2 file")?;
        Ok(())
    }
}

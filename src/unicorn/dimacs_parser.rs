use crate::unicorn::bitblasting::{Gate, GateModel, GateRef};
use crate::unicorn::{Node, NodeType};
use anyhow::{Context, Result};
use regex::Regex;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;
use std::rc::Rc;
use std::str::FromStr;

//
// Public Interface
//

pub fn load_dimacs_as_gatemodel(path: &Path) -> Result<GateModel> {
    let mut parser = DimacsParser::new();
    parser.parse_dimacs_text_file(path)?;
    Ok(parser.into_model())
}

//
// Private Implementation
//

fn input_gate(i: usize) -> GateRef {
    let name = format!("b{}", i);
    GateRef::from(Gate::InputBit { name })
}

fn not_gate(a: GateRef) -> GateRef {
    GateRef::from(Gate::Not { value: a })
}

fn or_gate(a: GateRef, b: GateRef) -> GateRef {
    GateRef::from(Gate::Or { left: a, right: b })
}

fn and_gate(a: GateRef, b: GateRef) -> GateRef {
    GateRef::from(Gate::And { left: a, right: b })
}

struct DimacsParser {
    num_variables: usize,
    num_clauses: usize,
    gate_variables: Vec<GateRef>,
    gate_negations: Vec<GateRef>,
    gate_clauses: Vec<GateRef>,
}

impl DimacsParser {
    fn new() -> Self {
        Self {
            num_variables: 0,
            num_clauses: 0,
            gate_variables: Vec::new(),
            gate_negations: Vec::new(),
            gate_clauses: Vec::new(),
        }
    }

    fn initialize_variables(&mut self) {
        assert!(self.gate_variables.is_empty());
        assert!(self.gate_negations.is_empty());
        for i in 0..self.num_variables {
            let gate_var = input_gate(i);
            let gate_neg = not_gate(gate_var.clone());
            self.gate_variables.push(gate_var);
            self.gate_negations.push(gate_neg);
        }
    }

    fn literal_to_gate(&self, literal: i32) -> GateRef {
        if literal < 0 {
            self.gate_negations[i32::abs(literal) as usize - 1].clone()
        } else {
            self.gate_variables[literal as usize - 1].clone()
        }
    }

    fn add_clause(&mut self, literals: Vec<i32>) {
        let gate_literals = literals.iter().map(|l| self.literal_to_gate(*l));
        let gate = gate_literals.reduce(or_gate).unwrap();
        self.gate_clauses.push(gate);
    }

    fn into_model(self) -> GateModel {
        let gate = self.gate_clauses.into_iter().reduce(and_gate).unwrap();
        // TODO: The fact that we are requiring a node here just to communicate
        // random Nid values to Qubot is a bit of a hack. Fix this!
        let node = Rc::new(RefCell::new(Node::Input {
            nid: 99999999,
            sort: NodeType::Bit,
            name: "from-dimacs-cnf".to_string(),
        }));
        GateModel {
            bad_state_gates: vec![gate],
            bad_state_nodes: vec![node],
            constraints: HashMap::new(),
            input_gates: Vec::new(),
            mapping: HashMap::new(),
            mapping_adders: HashMap::new(),
            constraint_based_dependencies: HashMap::new(),
            witness: None,
        }
    }

    fn parse_dimacs_text_file(&mut self, path: &Path) -> Result<()> {
        let re_magic: Regex = Regex::new(r"^p cnf ([0-9]+) ([0-9]+)$").unwrap();
        let re_clause: Regex = Regex::new(r"^((-?[1-9][0-9]* )+)0$").unwrap();

        let mut has_seen_magic_line = false;

        let file = File::open(path)?;
        let reader = BufReader::new(file);
        for line in reader.lines() {
            let line = line.unwrap();

            // Skip all comment lines.
            if line.starts_with("c ") {
                continue;
            }

            // Recognize CNF magic line.
            if let Some(caps) = re_magic.captures(&line) {
                assert!(!has_seen_magic_line);
                let num_variables = caps.get(1).context("missing #variables")?;
                let num_clauses = caps.get(2).context("missing #clauses")?;
                self.num_variables = usize::from_str(num_variables.as_str())?;
                self.num_clauses = usize::from_str(num_clauses.as_str())?;
                self.initialize_variables();
                has_seen_magic_line = true;
                continue;
            }

            // Recognize a clause line.
            if let Some(caps) = re_clause.captures(&line) {
                assert!(has_seen_magic_line);
                let clause = caps.get(1).context("missing literals")?.as_str().trim();
                self.add_clause(
                    clause
                        .split(' ')
                        .map(|l| i32::from_str(l).expect("range"))
                        .collect(),
                );
                continue;
            }

            panic!("Unrecognized line: {}", line);
        }

        assert!(self.gate_variables.len() == self.num_variables);
        assert!(self.gate_negations.len() == self.num_variables);
        assert!(self.gate_clauses.len() == self.num_clauses);
        Ok(())
    }
}

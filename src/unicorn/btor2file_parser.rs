use crate::unicorn::{get_nodetype, Model, Nid, Node, NodeRef};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::ops::Range;
use std::path::Path;

pub fn parse_btor2_file(path: &Path) -> Model {
    let mut parser = BTOR2Parser::new();
    parser.parse_file(path);
    parser.run_inits();
    Model {
        lines: Vec::new(),
        sequentials: parser.get_sequentials(),
        bad_states_initial: Vec::new(),
        bad_states_sequential: parser.get_bad_state_sequentials(),
        data_range: Range { start: 0, end: 0 },
        heap_range: Range { start: 0, end: 0 },
        stack_range: Range { start: 0, end: 0 },
        memory_size: 0,
    }
}

struct BTOR2Parser {
    mapping: HashMap<Nid, NodeRef>,
    lines: HashMap<Nid, Vec<String>>,
}

impl BTOR2Parser {
    fn new() -> Self {
        Self {
            mapping: HashMap::new(),
            lines: HashMap::new(),
        }
    }

    fn read_lines<P>(&self, filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
    where
        P: AsRef<Path>,
    {
        let file = File::open(filename)?;
        Ok(io::BufReader::new(file).lines())
    }

    fn parse_file(&mut self, path: &Path) {
        if let Ok(lines) = self.read_lines(path) {
            for line in lines.flatten() {
                let mut cleaned_line = line.trim();
                if let Some(comment_start_index) = cleaned_line.find(';') {
                    cleaned_line = &cleaned_line[comment_start_index..];
                }

                let elements: Vec<&str> = cleaned_line.split(' ').collect();

                let mut parsed_line: Vec<String> = Vec::new();

                for element in elements {
                    if !element.is_empty() {
                        parsed_line.push(element.to_string());
                    }
                }

                if !parsed_line.is_empty() {
                    if let Ok(nid) = parsed_line[0].parse::<u64>() {
                        self.lines.insert(nid, parsed_line);
                    } else {
                        panic!("could not parse line->'{:?}'", parsed_line);
                    }
                }
            }
        } else {
            println!("Error reading file ({:?})", path);
        }
    }

    fn process_node(&mut self, nid: Nid) -> NodeRef {
        let mut current_node: Option<NodeRef> = None;
        let line = self.lines.get(&nid).unwrap().clone();

        if let Ok(sort) = line[2].parse::<usize>() {
            if self.mapping.contains_key(&nid) {
                return self.mapping.get(&nid).unwrap().clone();
            }

            let operator_name = line[1].to_lowercase();

            match operator_name.as_str() {
                "const" => {
                    if let Ok(imm) = line[3].parse::<u64>() {
                        current_node = Some(NodeRef::from(Node::Const {
                            nid,
                            sort: get_nodetype(sort),
                            imm,
                        }));
                    } else {
                        panic!("not valid imm for const operator ({})", line[3]);
                    }
                }
                "input" => {
                    current_node = Some(NodeRef::from(Node::Input {
                        nid,
                        sort: get_nodetype(sort),
                        name: "input".to_string(),
                    }))
                }
                "init" => {
                    if let Ok(nid_state) = line[3].parse::<Nid>() {
                        if let Ok(nid_value) = line[4].parse::<Nid>() {
                            let state_ref = self.process_node(nid_state);
                            let value_ref = self.process_node(nid_value);
                            match &*state_ref.borrow() {
                                Node::State { .. } => {
                                    current_node = Some(NodeRef::from(Node::State {
                                        nid: nid_state,
                                        sort: get_nodetype(sort),
                                        init: Some(value_ref),
                                        name: None,
                                    }));
                                    self.mapping.insert(nid_state, current_node.unwrap());
                                }
                                _ => {
                                    panic!("invalid init!");
                                }
                            };
                        }
                    }
                    panic!("Error parsing init ({:?})", line);
                }
                "state" => {
                    current_node = Some(NodeRef::from(Node::State {
                        nid,
                        sort: get_nodetype(sort),
                        init: None,
                        name: None,
                    }));
                }
                "not" | "bad" => {
                    if let Ok(nid_value) = line[3].parse::<Nid>() {
                        let value = self.process_node(nid_value);

                        match operator_name.as_str() {
                            "not" => current_node = Some(NodeRef::from(Node::Not { nid, value })),
                            "bad" => {
                                current_node = Some(NodeRef::from(Node::Bad {
                                    nid,
                                    cond: value,
                                    name: None,
                                }))
                            }
                            _ => {
                                panic!("this piece of code should be unreacheable");
                            }
                        }
                    }
                }
                "ite" => {
                    // TODO: handle negative conditions
                    if let Ok(nid_condition) = line[3].parse::<Nid>() {
                        if let Ok(nid_truth_part) = line[4].parse::<Nid>() {
                            if let Ok(nid_false_part) = line[5].parse::<Nid>() {
                                let cond = self.process_node(nid_condition);
                                let left = self.process_node(nid_truth_part);
                                let right = self.process_node(nid_false_part);

                                current_node = Some(NodeRef::from(Node::Ite {
                                    nid,
                                    sort: get_nodetype(sort),
                                    cond,
                                    left,
                                    right,
                                }))
                            }
                        }
                    }
                }
                "add" | "sub" | "mul" | "udiv" | "urem" | "ult" | "eq" | "and" | "next" => {
                    if let Ok(nid_left) = line[3].parse::<Nid>() {
                        if let Ok(nid_right) = line[4].parse::<Nid>() {
                            let left = self.process_node(nid_left);
                            let right = self.process_node(nid_right);

                            let temp_node: Node;

                            match operator_name.as_str() {
                                "add" => {
                                    temp_node = Node::Add { nid, left, right };
                                }
                                "sub" => {
                                    temp_node = Node::Sub { nid, left, right };
                                }
                                "mul" => temp_node = Node::Mul { nid, left, right },
                                "udiv" => temp_node = Node::Div { nid, left, right },
                                "urem" => temp_node = Node::Rem { nid, left, right },
                                "ult" => temp_node = Node::Ult { nid, left, right },
                                "eq" => temp_node = Node::Eq { nid, left, right },
                                "and" => temp_node = Node::And { nid, left, right },
                                "next" => {
                                    temp_node = Node::Next {
                                        nid,
                                        sort: get_nodetype(sort),
                                        state: left,
                                        next: right,
                                    }
                                }
                                _ => {
                                    panic!("This piece of code should be unreacheable");
                                }
                            }
                            current_node = Some(NodeRef::from(temp_node));
                        }
                    }
                }
                "ext" | "read" | "write" => {
                    // TODO implement these btor2 operators
                    panic!("BTOR2 operator not implemented!");
                }
                _ => {
                    panic!("Not supported btor2 operator {}", operator_name);
                }
            }
            if let Some(answer) = current_node {
                self.mapping.insert(nid, answer.clone());
                return answer;
            } else {
                panic!("could not parse {:?}", line);
            }
        }

        panic!("error parsing nid {} ", line[0]);
    }

    fn run_inits(&mut self) {
        for (nid, line) in self.lines.clone() {
            if line[1].to_lowercase() == "init" {
                self.process_node(nid);
            }
        }
    }
    fn get_sequentials(&mut self) -> Vec<NodeRef> {
        let mut result: Vec<NodeRef> = Vec::new();

        for (nid, line) in self.lines.clone() {
            if line[1].to_lowercase() == "next" {
                result.push(self.process_node(nid));
            }
        }
        result
    }

    fn get_bad_state_sequentials(&mut self) -> Vec<NodeRef> {
        let mut result: Vec<NodeRef> = Vec::new();

        for (nid, line) in self.lines.clone() {
            if line[1].to_lowercase() == "bad" {
                result.push(self.process_node(nid));
            }
        }

        result
    }
}

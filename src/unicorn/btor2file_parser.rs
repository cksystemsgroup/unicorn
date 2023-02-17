use crate::unicorn::{get_nodetype, Model, Nid, Node, NodeRef, NodeType};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::ops::Range;
use std::path::Path;

//
// Public Interface
//

pub fn parse_btor2_file(path: &Path) -> Model {
    let mut parser = BTOR2Parser::new();
    parser.parse_file(path);
    parser.run_inits();
    let (bad_states_initial, bad_states_sequential) = parser
        .get_bad_states()
        .into_iter()
        .partition(has_depth_in_name);
    Model {
        lines: Vec::new(),
        sequentials: parser.get_sequentials(),
        bad_states_initial,
        bad_states_sequential,
        data_range: Range { start: 0, end: 0 },
        heap_range: Range { start: 0, end: 0 },
        stack_range: Range { start: 0, end: 0 },
        memory_size: 0,
    }
}

//
// Private Implementation
//

struct BTOR2Parser {
    mapping: HashMap<Nid, NodeRef>,
    lines: HashMap<Nid, Vec<String>>,
}

fn has_depth_in_name(bad_state: &NodeRef) -> bool {
    if let Node::Bad {
        name: Some(name), ..
    } = &*bad_state.borrow()
    {
        name.contains("[n=")
    } else {
        false
    }
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

    fn parse_lines(&mut self, lines: &[String]) {
        for line in lines {
            let mut cleaned_line = line.trim();
            if let Some(comment_start_index) = cleaned_line.find(';') {
                cleaned_line = &cleaned_line[..comment_start_index];
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
    }

    fn parse_file(&mut self, path: &Path) {
        if let Ok(lines) = self.read_lines(path) {
            let flattened_lines: Vec<String> = lines.flatten().collect();
            self.parse_lines(&flattened_lines);
        } else {
            println!("Error reading file ({:?})", path);
        }
    }

    fn get_sort(&self, nid: Nid) -> NodeType {
        let line = self.lines.get(&nid).unwrap().clone();
        if line[2] == "bitvec" {
            if let Ok(answer) = line[3].parse::<usize>() {
                return get_nodetype(answer);
            }
            panic!("Unsupported bitvec: {:?}", line);
        } else if line[2] == "array" {
            if let Ok(sort_idx) = line[3].parse::<Nid>() {
                if let Ok(sort_val) = line[4].parse::<Nid>() {
                    if self.get_sort(sort_idx) == NodeType::Word
                        && self.get_sort(sort_val) == NodeType::Word
                    {
                        return NodeType::Memory;
                    }
                }
            }
            panic!("Unsupported array: {:?}", line);
        } else {
            panic!("Invalid sort: {:?}", line);
        }
    }

    fn process_node(&mut self, nid: Nid) -> NodeRef {
        if self.mapping.contains_key(&nid) {
            return self.mapping.get(&nid).unwrap().clone();
        }

        let mut current_node: Option<NodeRef> = None;
        let line = self.lines.get(&nid).unwrap().clone();
        let operator_name = line[1].to_lowercase();
        let sort = if let Ok(sort_nid) = line[2].parse::<Nid>() {
            if operator_name != "bad" {
                self.get_sort(sort_nid)
            } else {
                NodeType::Bit
            }
        } else {
            panic!("error parsing nid {} ", line[0]);
        };

        match operator_name.as_str() {
            "constd" => {
                if let Ok(imm) = line[3].parse::<u64>() {
                    current_node = Some(NodeRef::from(Node::Const { nid, sort, imm }));
                } else {
                    panic!("not valid imm for const operator ({})", line[3]);
                }
            }
            "input" => {
                current_node = Some(NodeRef::from(Node::Input {
                    nid,
                    sort,
                    name: "input".to_string(),
                }))
            }
            "init" => {
                if let Ok(nid_state) = line[3].parse::<Nid>() {
                    if let Ok(nid_value) = line[4].parse::<Nid>() {
                        let state_ref = self.process_node(nid_state);
                        let value_ref = self.process_node(nid_value);
                        match &*state_ref.borrow() {
                            Node::State { name, .. } => {
                                let modified_state = NodeRef::from(Node::State {
                                    nid: nid_state,
                                    sort,
                                    init: Some(value_ref),
                                    name: name.clone(),
                                });
                                current_node = Some(modified_state.clone());
                                self.mapping.insert(nid_state, modified_state);
                            }
                            _ => {
                                panic!("invalid init!");
                            }
                        };
                    }
                }
            }
            "state" => {
                let name = line.get(3).cloned();
                current_node = Some(NodeRef::from(Node::State {
                    nid,
                    sort,
                    init: None,
                    name,
                }));
            }
            "not" => {
                if let Ok(nid_value) = line[3].parse::<Nid>() {
                    let value = self.process_node(nid_value);
                    current_node = Some(NodeRef::from(Node::Not { nid, sort, value }))
                }
            }
            "bad" => {
                if let Ok(nid_value) = line[2].parse::<Nid>() {
                    let name = line.get(3).cloned();
                    let value = self.process_node(nid_value);
                    current_node = Some(NodeRef::from(Node::Bad {
                        nid,
                        cond: value,
                        name,
                    }))
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
                                sort,
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

                        let temp_node = match operator_name.as_str() {
                            "add" => Node::Add { nid, left, right },
                            "sub" => Node::Sub { nid, left, right },
                            "mul" => Node::Mul { nid, left, right },
                            "udiv" => Node::Divu { nid, left, right },
                            "urem" => Node::Rem { nid, left, right },
                            "ult" => Node::Ult { nid, left, right },
                            "eq" => Node::Eq { nid, left, right },
                            "and" => Node::And {
                                nid,
                                sort,
                                left,
                                right,
                            },
                            "next" => Node::Next {
                                nid,
                                sort,
                                state: left,
                                next: right,
                            },
                            _ => {
                                panic!("This piece of code should be unreacheable");
                            }
                        };
                        current_node = Some(NodeRef::from(temp_node));
                    }
                }
            }
            "uext" => {
                if let Ok(nid_value) = line[3].parse::<Nid>() {
                    if let Ok(bits_ext) = line[4].parse::<usize>() {
                        let value = self.process_node(nid_value);
                        let bits_dest = sort.bitsize();
                        let bits_src = bits_dest - bits_ext;
                        current_node = Some(NodeRef::from(Node::Ext {
                            nid,
                            from: get_nodetype(bits_src),
                            value,
                        }))
                    }
                }
            }
            "read" => {
                if let Ok(nid_memory) = line[3].parse::<Nid>() {
                    if let Ok(nid_address) = line[4].parse::<Nid>() {
                        let memory = self.process_node(nid_memory);
                        let address = self.process_node(nid_address);
                        current_node = Some(NodeRef::from(Node::Read {
                            nid,
                            memory,
                            address,
                        }))
                    }
                }
            }
            "write" => {
                if let Ok(nid_memory) = line[3].parse::<Nid>() {
                    if let Ok(nid_address) = line[4].parse::<Nid>() {
                        if let Ok(nid_value) = line[5].parse::<Nid>() {
                            let memory = self.process_node(nid_memory);
                            let address = self.process_node(nid_address);
                            let value = self.process_node(nid_value);
                            current_node = Some(NodeRef::from(Node::Write {
                                nid,
                                memory,
                                address,
                                value,
                            }))
                        }
                    }
                }
            }
            _ => {
                panic!("Unsupported BTOR2 operator: {}", operator_name);
            }
        }

        if let Some(answer) = current_node {
            self.mapping.insert(nid, answer.clone());
            answer
        } else {
            panic!("could not parse {:?}", line);
        }
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

    fn get_bad_states(&mut self) -> Vec<NodeRef> {
        let mut result: Vec<NodeRef> = Vec::new();

        for (nid, line) in self.lines.clone() {
            if line[1].to_lowercase() == "bad" {
                result.push(self.process_node(nid));
            }
        }
        result
    }
}

#[cfg(test)]
mod tests_btor2_parser {
    use super::*;
    use crate::unicorn::bitblasting::bitblast_model;
    use crate::unicorn::qubot::{InputEvaluator, Qubot};

    fn get_model(file: &str) -> Model {
        let mut parser = BTOR2Parser::new();
        let lines: Vec<String> = file.split('\n').map(|s| s.to_string()).collect();
        parser.parse_lines(&lines);
        parser.run_inits();
        Model {
            lines: Vec::new(),
            sequentials: parser.get_sequentials(),
            bad_states_initial: parser.get_bad_states(),
            bad_states_sequential: Vec::new(),
            data_range: Range { start: 0, end: 0 },
            heap_range: Range { start: 0, end: 0 },
            stack_range: Range { start: 0, end: 0 },
            memory_size: 0,
        }
    }
    #[test]
    fn test_add() {
        let file = "1 sort bitvec 8
        2 input 1
        3 input 1
        4 add 1 2 3
        5 constd 1 118
        6 eq 1 4 5
        7 bad 6
        ";
        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                    &qubot.qubo,
                    &qubot.mapping,
                    &all_inputs,
                    &[i, j],
                    bad_state_qubits.clone(),
                );

                let local_result = (i + j) & 255;
                if final_offset == 0.0 {
                    assert!(local_result == 118);
                } else {
                    assert!(local_result != 118);
                }
            }
        }
    }

    #[test]
    fn test_and() {
        let file = "1 sort bitvec 8
        2 input 1
        3 input 1
        4 and 1 2 3
        5 constd 1 118
        6 eq 1 4 5
        7 bad 6
        ";
        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                    &qubot.qubo,
                    &qubot.mapping,
                    &all_inputs,
                    &[i, j],
                    bad_state_qubits.clone(),
                );
                let local_result = i & j;
                if final_offset == 0.0 {
                    assert!(local_result == 118);
                } else {
                    assert!(local_result != 118);
                }
            }
        }
    }

    #[test]
    fn test_div() {
        let file = "1 sort bitvec 8
        2 input 1
        3 input 1
        4 udiv 1 2 3
        5 constd 1 2
        6 eq 1 4 5
        7 bad 6
        ";
        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                if j > 0 {
                    // avoid division by zero
                    let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                        &qubot.qubo,
                        &qubot.mapping,
                        &all_inputs,
                        &[i, j],
                        bad_state_qubits.clone(),
                    );

                    let local_result: i64 = i / j;

                    if local_result == 2 {
                        assert!(final_offset == 0.0);
                    } else {
                        assert!(final_offset > 0.0);
                    }
                }
            }
        }
    }

    #[test]
    fn test_eq() {
        let file = "1 sort bitvec 8
        2 input 1
        3 input 1
        4 eq 1 2 3
        5 bad 4
        ";

        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                    &qubot.qubo,
                    &qubot.mapping,
                    &all_inputs,
                    &[i, j],
                    bad_state_qubits.clone(),
                );
                if final_offset == 0.0 {
                    assert!(i == j);
                } else {
                    assert!(i != j);
                }
            }
        }
    }

    #[test]
    fn test_ite() {
        let file = "1 sort bitvec 8
        2 sort bitvec 1
        3 input 1
        4 input 1
        5 input 2
        6 ite 1 5 3 4
        7 constd 1 118
        8 eq 2 6 7
        9 bad 8
        ";
        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 3);
        assert!(all_inputs[0].1.len() == 1);
        assert!(all_inputs[1].1.len() == 8);
        assert!(all_inputs[1].1.len() == all_inputs[1].1.len());

        for c in 0..2 {
            for i in 0..256 {
                for j in 0..256 {
                    let mut input_evaluator = InputEvaluator::new();
                    let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                        &qubot.qubo,
                        &qubot.mapping,
                        &all_inputs,
                        &[c, i, j],
                        bad_state_qubits.clone(),
                    );
                    if final_offset == 0.0 {
                        if c == 1 {
                            assert!(i == 118);
                        } else {
                            assert!(j == 118);
                        }
                    } else if c == 1 {
                        assert!(i != 118);
                    } else {
                        assert!(j != 118);
                    }
                }
            }
        }
    }

    #[test]
    fn test_mul() {
        let file = "1 sort bitvec 8
        2 input 1
        3 input 1
        4 mul 1 2 3
        5 constd 1 118
        6 eq 1 4 5
        7 bad 6
        ";
        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                    &qubot.qubo,
                    &qubot.mapping,
                    &all_inputs,
                    &[i, j],
                    bad_state_qubits.clone(),
                );

                let local_result = (i * j) & 255;
                if final_offset == 0.0 {
                    assert!(local_result == 118);
                } else {
                    assert!(local_result != 118);
                }
            }
        }
    }

    #[test]
    fn test_not() {
        let file = "1 sort bitvec 8
        2 input 1
        4 not 1 2
        5 constd 1 118
        6 eq 1 4 5
        7 bad 6
        ";
        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 1);
        assert!(all_inputs[0].1.len() == 8);

        for i in 0..256 {
            let mut input_evaluator = InputEvaluator::new();
            let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                &qubot.qubo,
                &qubot.mapping,
                &all_inputs,
                &[i],
                bad_state_qubits.clone(),
            );

            let local_result = !i & 255;
            if final_offset == 0.0 {
                assert!(local_result == 118);
            } else {
                assert!(local_result != 118);
            }
        }
    }

    #[test]
    fn test_rem() {
        let file = "1 sort bitvec 8
        2 input 1
        3 input 1
        4 urem 1 2 3
        5 constd 1 118
        6 eq 1 4 5
        7 bad 6
        ";
        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                if j > 0 {
                    // avoid division by zero
                    let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                        &qubot.qubo,
                        &qubot.mapping,
                        &all_inputs,
                        &[i, j],
                        bad_state_qubits.clone(),
                    );

                    let local_result: i64 = i % j;
                    if final_offset == 0.0 {
                        assert!(local_result == 118);
                    } else {
                        assert!(local_result != 118);
                    }
                }
            }
        }
    }

    #[test]
    fn test_sub() {
        let file = "1 sort bitvec 8
        2 input 1
        3 input 1
        4 sub 1 2 3
        5 constd 1 118
        6 eq 1 4 5
        7 bad 6
        ";

        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                    &qubot.qubo,
                    &qubot.mapping,
                    &all_inputs,
                    &[i, j],
                    bad_state_qubits.clone(),
                );

                let local_result = (i - j) & 255;
                if final_offset == 0.0 {
                    assert!(local_result == 118);
                } else {
                    assert!(local_result != 118);
                }
            }
        }
    }

    #[test]
    fn test_ult() {
        let file = "1 sort bitvec 8
        2 sort bitvec 1
        3 input 1
        4 input 1
        5 ult 1 3 4
        6 constd 2 1
        7 eq 1 5 6
        8 bad 7
        ";

        let model = get_model(file);
        let gate_model = bitblast_model(&model, true, 64);
        let mut qubot = Qubot::new(&gate_model, false);

        let bad_state_qubits = qubot.build_qubo();
        let all_inputs = gate_model.input_gates.clone();
        assert!(all_inputs.len() == 2);
        assert!(all_inputs[0].1.len() == 8);
        assert!(all_inputs[0].1.len() == all_inputs[1].1.len());

        for i in 0..256 {
            for j in 0..256 {
                let mut input_evaluator = InputEvaluator::new();
                let (final_offset, _true_bad_states) = input_evaluator.evaluate_inputs(
                    &qubot.qubo,
                    &qubot.mapping,
                    &all_inputs,
                    &[i, j],
                    bad_state_qubits.clone(),
                );

                let local_result = i < j;
                if final_offset == 0.0 {
                    assert!(local_result);
                } else {
                    assert!(!local_result);
                }
            }
        }
    }
}

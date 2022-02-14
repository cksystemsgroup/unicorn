use crate::modeler::{HashableNodeRef, Model, Node, NodeRef, NodeType};
use log::{info, warn};
use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// public interface

// pub fn bitblast_model(model: Model, constant_propagation: bool, word_size: u64) -> Vec<GateRef> {
//     let mut bitblasting = BitBlasting::new(&model, constant_propagation, word_size);
//     bitblasting.process_model(&model)
// }

pub type GateRef = Rc<RefCell<Gate>>;

#[derive(Debug, PartialEq, Eq)]
pub enum Gate {
    ConstTrue,
    ConstFalse,
    InputBit {
        name: String,
    },
    Not {
        value: GateRef,
    },
    And {
        left: GateRef,
        right: GateRef,
    },
    Nand {
        left: GateRef,
        right: GateRef,
    },
    Or {
        left: GateRef,
        right: GateRef,
    },
    Matriarch1 {
        cond: GateRef,
        right: GateRef,
    },
    CarryHalfAdder {
        left: GateRef,
        right: GateRef,
    },
    ResultHalfAdder {
        input1: GateRef,
        input2: GateRef,
    },
    CarryFullAdder {
        input1: GateRef,
        input2: GateRef,
        input3: GateRef,
    },
    ResultFullAdder {
        input1: GateRef,
        input2: GateRef,
        input3: GateRef,
    },
}

impl From<Gate> for GateRef {
    fn from(gate: Gate) -> Self {
        Rc::new(RefCell::new(gate))
    }
}

#[derive(Debug)]
pub struct HashableGateRef {
    value: GateRef,
    //name: String
}

impl Eq for HashableGateRef {}

// pub fn get_gate_name(gate: &GateRef ) -> String{
//     match &*gate.borrow() {
//         Gate::And {..} => {"AND".to_string()},
//         Gate::CarryFullAdder {..} => {"CarryFA".to_string()}
//         Gate::CarryHalfAdder  {..} => {"CarryHA".to_string()}
//         Gate::ConstFalse  {..} =>{"false".to_string()}
//         Gate::ConstTrue {..} => {"true".to_string()}
//         Gate::InputBit  {..} =>{"input".to_string()}
//         Gate::Matriarch1  {..} =>{"matriarch1".to_string()}
//         Gate::Nand  {..} => { "NAND".to_string()}
//         Gate::Not  {..} => { "Not".to_string()}
//         Gate::Or  {..} => {"Or".to_string()}
//         Gate::ResultFullAdder  {..} => { "ResFA".to_string()}
//         Gate::ResultHalfAdder  {..} =>{ "ResHA".to_string()}
//     }
// }

impl From<GateRef> for HashableGateRef {
    fn from(node: GateRef) -> Self {
        Self {
            value: node, /*name: get_gate_name(&node)*/
        }
    }
}

impl Hash for HashableGateRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

pub fn get_addresses_gates(model: &Model, word_size: &u64) -> Vec<Vec<GateRef>> {
    // TODO: test
    let mut result = Vec::new();

    for i in model.data_range.clone().step_by(*word_size as usize) {
        result.push(get_gates_from_numeric(i, &(*word_size as usize)));
    }

    for i in model.heap_range.clone().step_by(*word_size as usize) {
        result.push(get_gates_from_numeric(i, &(*word_size as usize)));
    }

    for i in model.stack_range.clone().step_by(*word_size as usize) {
        result.push(get_gates_from_numeric(i, &(*word_size as usize)));
    }

    result
}

impl PartialEq for HashableGateRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}

fn get_gate_from_constant_bit(bit: u64) -> GateRef {
    assert!((bit == 0) | (bit == 1));
    if bit == 1 {
        GateRef::from(Gate::ConstTrue)
    } else {
        GateRef::from(Gate::ConstFalse)
    }
}

fn is_constant(gate_type: GateRef) -> bool {
    *gate_type == RefCell::new(Gate::ConstTrue) || *gate_type == RefCell::new(Gate::ConstFalse)
}

fn get_constant(gate_type: GateRef) -> Option<bool> {
    if is_constant(gate_type.clone()) {
        if *gate_type == RefCell::new(Gate::ConstFalse) {
            Some(false)
        } else {
            Some(true)
        }
    } else {
        None
    }
}

fn get_numeric_from_gate(gate_type: &GateRef) -> Option<u8> {
    if let Some(result) = get_constant(gate_type.clone()) {
        if result {
            Some(1)
        } else {
            Some(0)
        }
    } else {
        None
    }
}

pub fn get_numeric_from_gates(gates: &[GateRef]) -> u64 {
    let mut result: u64 = 0;

    for (exponent, gate) in gates.iter().enumerate() {
        if let Some(value) = get_numeric_from_gate(gate) {
            if value == 1 {
                result += (2_u64).pow(exponent as u32);
            }
        } else {
            panic!("Trying to get numeric value from non-const gate");
        }
    }

    result
}

fn get_gates_from_numeric(mut num: u64, size: &usize) -> Vec<GateRef> {
    let mut result: Vec<GateRef> = Vec::new();

    while result.len() < *size {
        result.push(get_gate_from_constant_bit(num % 2));
        num /= 2;
    }

    result
}

fn get_gate_from_boolean(a: bool) -> GateRef {
    if a {
        GateRef::from(Gate::ConstTrue)
    } else {
        GateRef::from(Gate::ConstFalse)
    }
}

fn are_there_false_constants(const1: Option<bool>, const2: Option<bool>) -> bool {
    if let Some(a) = const1 {
        if !a {
            return true;
        }
    }

    if let Some(b) = const2 {
        return !b;
    }
    false
}

fn are_there_true_constants(const1: Option<bool>, const2: Option<bool>) -> bool {
    if let Some(a) = const1 {
        if a {
            return true;
        }
    }

    if let Some(b) = const2 {
        return b;
    }
    false
}

fn are_both_constants(const1: Option<bool>, const2: Option<bool>) -> bool {
    if let Some(_a) = const1 {
        if let Some(_b) = const2 {
            return true;
        }
    }
    false
}

fn get_non_constant_gate(gates: &[GateRef]) -> Option<GateRef> {
    for gate in gates {
        if get_constant(gate.clone()).is_none() {
            return Some((*gate).clone());
        }
    }
    None
}

fn get_replacement_from_constant(sort: &NodeType, value_: u64) -> Vec<GateRef> {
    let total_bits = sort.bitsize();
    let mut replacement: Vec<GateRef> = Vec::new();
    let mut value = value_;
    for _ in 0..total_bits {
        replacement.push(get_gate_from_constant_bit(value % 2));
        value /= 2;
    }
    replacement
}

fn and_gate(a: Option<bool>, b: Option<bool>, a_gate: &GateRef, b_gate: &GateRef) -> GateRef {
    if are_both_constants(a, b) {
        let val_a = a.unwrap();
        let val_b = b.unwrap();

        if val_a {
            assert!(*a_gate == GateRef::from(Gate::ConstTrue));
        } else {
            assert!(*a_gate == GateRef::from(Gate::ConstFalse));
        }

        if val_b {
            assert!(*b_gate == GateRef::from(Gate::ConstTrue));
        } else {
            assert!(*b_gate == GateRef::from(Gate::ConstFalse));
        }

        get_gate_from_boolean(a.unwrap() && b.unwrap())
    } else if are_there_false_constants(a, b) {
        GateRef::from(Gate::ConstFalse)
    } else if are_there_true_constants(a, b) {
        get_non_constant_gate(&[a_gate.clone(), b_gate.clone()]).unwrap()
    } else {
        GateRef::from(Gate::And {
            left: a_gate.clone(),
            right: b_gate.clone(),
        })
    }
}

fn matriarch1_gate(
    cond: Option<bool>,
    b: Option<bool>,
    cond_gate: &GateRef,
    b_gate: &GateRef,
) -> GateRef {
    if are_both_constants(cond, b) {
        get_gate_from_boolean(!cond.unwrap() && b.unwrap())
    } else if let Some(const_cond) = get_constant(cond_gate.clone()) {
        if const_cond {
            GateRef::from(Gate::ConstFalse)
        } else {
            b_gate.clone()
        }
    } else if let Some(const_bit) = get_constant(b_gate.clone()) {
        if const_bit {
            GateRef::from(Gate::Not {
                value: cond_gate.clone(),
            })
        } else {
            GateRef::from(Gate::ConstFalse)
        }
    } else {
        GateRef::from(Gate::Matriarch1 {
            cond: cond_gate.clone(),
            right: b_gate.clone(),
        })
    }
}

fn or_gate(a: Option<bool>, b: Option<bool>, a_gate: &GateRef, b_gate: &GateRef) -> GateRef {
    if are_both_constants(a, b) {
        get_gate_from_boolean(a.unwrap() || b.unwrap())
    } else if are_there_true_constants(a, b) {
        GateRef::from(Gate::ConstTrue)
    } else if are_there_false_constants(a, b) {
        get_non_constant_gate(&[a_gate.clone(), b_gate.clone()]).unwrap()
    } else {
        GateRef::from(Gate::Or {
            left: a_gate.clone(),
            right: b_gate.clone(),
        })
    }
}

fn not_gate(a_gate: GateRef) -> GateRef {
    let a = get_constant(a_gate.clone());

    if let Some(a_const) = a {
        if a_const {
            GateRef::from(Gate::ConstFalse)
        } else {
            GateRef::from(Gate::ConstTrue)
        }
    } else {
        GateRef::from(Gate::Not { value: a_gate })
    }
}

fn xnor_gate(a: Option<bool>, b: Option<bool>, a_gate: &GateRef, b_gate: &GateRef) -> GateRef {
    if are_both_constants(a, b) {
        get_gate_from_boolean(a.unwrap() == b.unwrap())
    } else if are_there_false_constants(a, b) {
        let non_constant = get_non_constant_gate(&[(*a_gate).clone(), (*b_gate).clone()]).unwrap();
        GateRef::from(Gate::Not {
            value: non_constant,
        })
    } else if are_there_true_constants(a, b) {
        get_non_constant_gate(&[a_gate.clone(), b_gate.clone()]).unwrap()
    } else {
        let not_a = GateRef::from(Gate::Not {
            value: a_gate.clone(),
        });
        let not_b = GateRef::from(Gate::Not {
            value: b_gate.clone(),
        });

        let nand1 = GateRef::from(Gate::Nand {
            left: (*a_gate).clone(),
            right: (*b_gate).clone(),
        });
        let nand2 = GateRef::from(Gate::Nand {
            left: not_a,
            right: not_b,
        });

        GateRef::from(Gate::Nand {
            left: nand1,
            right: nand2,
        })
    }
}

fn are_there_2_constants(bit1: &GateRef, bit2: &GateRef, bit3: &GateRef) -> bool {
    let const1 = get_constant(bit1.clone()).is_some() as u8;
    let const2 = get_constant(bit2.clone()).is_some() as u8;
    let const3 = get_constant(bit3.clone()).is_some() as u8;
    (const1 + const2 + const3) == 2
}

fn fold_bitwise_gate<F>(
    left: &[GateRef],
    right: &[GateRef],
    f_gate: F,
    _f_name: &str,
) -> Vec<GateRef>
where
    F: Fn(Option<bool>, Option<bool>, &GateRef, &GateRef) -> GateRef,
{
    assert!(left.len() == right.len());

    let mut replacement: Vec<GateRef> = Vec::new();

    for (l_bit, r_bit) in left.iter().zip(right.iter()) {
        let l_bit_const = get_constant(l_bit.clone());
        let r_bit_const = get_constant(r_bit.clone());
        replacement.push(f_gate(
            l_bit_const,
            r_bit_const,
            &(*l_bit).clone(),
            &(*r_bit).clone(),
        ));
    }
    replacement
}

fn fold_word_gate<F>(word: &[GateRef], f_gate: F, _f_name: &str) -> Vec<GateRef>
where
    F: Fn(Option<bool>, Option<bool>, &GateRef, &GateRef) -> GateRef,
{
    assert!(!word.is_empty());

    let mut current = word[0].clone();
    for w in word.iter().skip(1) {
        let a = get_constant(current.clone());
        let b = get_constant((*w).clone());
        current = f_gate(a, b, &current, &(*w).clone());
    }

    vec![current]
}

fn bitwise_equal(left_operand: &[GateRef], right_operand: &[GateRef]) -> Vec<GateRef> {
    let temp_word = fold_bitwise_gate(left_operand, right_operand, xnor_gate, "XNOR");
    fold_word_gate(&temp_word, and_gate, "WORD-AND")
}

pub struct BitBlasting<'a> {
    mapping: HashMap<HashableNodeRef, Vec<GateRef>>, // maps a btor2 operator to its resulting bitvector of gates
    // constant_propagation: bool, // TODO: make this flag work. Currently we always perform constant propagation
    pub constraints: HashMap<HashableGateRef, bool>, // this is for remainder and division, these are constraint based.
    word_size: u64, // I use this attribute as a variable because maybe we will do variable-length addresses? I only use this for reads and writes.
    model: &'a Model, // BTOR2 model
    addresses_gates: Vec<Vec<GateRef>>, // memory addresses represented as vectors of (constant-)gates
    pub mapping_adders: HashMap<HashableGateRef, GateRef>,
    pub input_gates: Vec<(NodeRef, Vec<GateRef>)>,
    pub gates_to_bad_nids: HashMap<HashableGateRef, NodeRef>,
    pub nid_to_gates: HashMap<u64, Vec<GateRef>>,
    pub constrain_based_dependencies: HashMap<GateRef, (Vec<GateRef>, Vec<GateRef>)>, // used or division and remainder, and when qubot whats to test an input (InputEvaluator).
}

impl<'a> BitBlasting<'a> {
    pub fn new(model_: &'a Model, _constant_propagation_: bool, word_size_: u64) -> Self {
        Self {
            mapping: HashMap::new(),
            //constant_propagation: constant_propagation_,
            constraints: HashMap::new(),
            word_size: word_size_,
            model: model_,
            addresses_gates: get_addresses_gates(model_, &word_size_),
            mapping_adders: HashMap::new(),
            input_gates: Vec::new(),
            gates_to_bad_nids: HashMap::new(),
            nid_to_gates: HashMap::new(),
            constrain_based_dependencies: HashMap::new(),
        }
    }

    fn get_2s_complement(&mut self, bitvector: Vec<GateRef>) -> Vec<GateRef> {
        // invert bits

        let mut inverted_bits: Vec<GateRef> = Vec::new();

        for bit in bitvector {
            inverted_bits.push(not_gate(bit));
        }

        // build a bitvector that represents 1

        let mut bitvector_1: Vec<GateRef> = vec![GateRef::from(Gate::ConstTrue)];

        assert!(bitvector_1.len() < inverted_bits.len());
        while bitvector_1.len() != inverted_bits.len() {
            bitvector_1.push(GateRef::from(Gate::ConstFalse));
        }

        self.bitwise_add(&inverted_bits, &bitvector_1, false)
    }

    fn bitwise_substraction(&mut self, left: Vec<GateRef>, right: Vec<GateRef>) -> Vec<GateRef> {
        let right_2s_complement = self.get_2s_complement(right);
        self.bitwise_add(&left, &right_2s_complement, false)
    }

    fn bitwise_add(
        &mut self,
        left: &[GateRef],
        right: &[GateRef],
        fix_last_carry: bool,
    ) -> Vec<GateRef> {
        fn get_2_constants(
            bit1: Option<bool>,
            bit2: Option<bool>,
            bit3: Option<bool>,
        ) -> (bool, bool) {
            if let Some(const1) = bit1 {
                if let Some(const2) = bit2 {
                    (const1, const2)
                } else if let Some(const3) = bit3 {
                    (const1, const3)
                } else {
                    panic!("Expecting 2 constants")
                }
            } else if let Some(const2) = bit2 {
                if let Some(const3) = bit3 {
                    (const2, const3)
                } else {
                    panic!("Expecting 2 constants")
                }
            } else {
                panic!("Expecting 2 constants")
            }
        }

        assert!(left.len() == right.len());
        let mut replacement: Vec<GateRef> = Vec::new();
        let mut carry: GateRef = GateRef::from(Gate::ConstFalse); // initlaize so compiler not complains
        let mut is_first = true;
        for (l_bit, r_bit) in left.iter().zip(right.iter()) {
            let l_const = get_constant(l_bit.clone());
            let r_const = get_constant(r_bit.clone());
            if is_first {
                // half adders
                if are_both_constants(l_const, r_const) {
                    carry = get_gate_from_boolean(l_const.unwrap() && r_const.unwrap());
                    replacement.push(get_gate_from_boolean(l_const.unwrap() != r_const.unwrap()));
                } else if are_there_false_constants(l_const, r_const) {
                    carry = GateRef::from(Gate::ConstFalse);
                    let non_constant =
                        get_non_constant_gate(&[l_bit.clone(), r_bit.clone()]).unwrap();
                    replacement.push(non_constant);
                } else if are_there_true_constants(l_const, r_const) {
                    let non_constant =
                        get_non_constant_gate(&[l_bit.clone(), r_bit.clone()]).unwrap();
                    carry = non_constant.clone();
                    replacement.push(GateRef::from(Gate::Not {
                        value: non_constant,
                    }));
                } else {
                    carry = GateRef::from(Gate::CarryHalfAdder {
                        left: (*l_bit).clone(),
                        right: (*r_bit).clone(),
                    });
                    let result = GateRef::from(Gate::ResultHalfAdder {
                        input1: (*l_bit).clone(),
                        input2: (*r_bit).clone(),
                    });
                    self.record_mapping_adders(&carry, &result);
                    self.record_mapping_adders(&result, &carry);
                    replacement.push(result);
                }
                is_first = false;
            // Full adders
            } else if are_both_constants(l_const, r_const) && is_constant(carry.clone()) {
                let carry_const = get_constant(carry.clone());
                let result = ((l_const.unwrap() as u64)
                    + (r_const.unwrap() as u64)
                    + (carry_const.unwrap() as u64))
                    % 2;

                replacement.push(get_gate_from_constant_bit(result));

                let temp = ((l_const.unwrap() as u8)
                    + (r_const.unwrap() as u8)
                    + (carry_const.unwrap() as u8))
                    > 1;
                carry = get_gate_from_boolean(temp);
            } else if are_there_2_constants(l_bit, r_bit, &carry) {
                let carry_const = get_constant(carry.clone());
                let (const1, const2) = get_2_constants(l_const, r_const, carry_const);
                if let Some(non_const) =
                    get_non_constant_gate(&[(*l_bit).clone(), (*r_bit).clone(), carry.clone()])
                {
                    if const1 && const2 {
                        carry = GateRef::from(Gate::ConstTrue);
                        replacement.push(non_const);
                    } else if const1 != const2 {
                        carry = non_const.clone();
                        replacement.push(GateRef::from(Gate::Not { value: non_const }));
                    } else {
                        carry = GateRef::from(Gate::ConstFalse);
                        replacement.push(non_const);
                    }
                } else {
                    panic!("bug in building addition circuit")
                }
            } else {
                // no constant propagation is possible
                let result = GateRef::from(Gate::ResultFullAdder {
                    input1: (*l_bit).clone(),
                    input2: (*r_bit).clone(),
                    input3: carry.clone(),
                });
                carry = GateRef::from(Gate::CarryFullAdder {
                    input1: (*l_bit).clone(),
                    input2: (*r_bit).clone(),
                    input3: carry.clone(),
                });
                self.record_mapping_adders(&carry, &result);
                self.record_mapping_adders(&result, &carry);
                replacement.push(result);
            }
        }

        if fix_last_carry {
            // when performing division (remainder) we need to set this constraint so the combinatorics of overflow is not doable.
            self.record_constraint(&carry, false);
        }
        assert!(replacement.len() == left.len());
        replacement
    }

    fn bitwise_multiplication(&mut self, left: &[GateRef], right: &[GateRef]) -> Vec<GateRef> {
        fn mutiply_by_digit(
            left_operand: &[GateRef],
            digit: &GateRef,
            shift: usize,
        ) -> Vec<GateRef> {
            let mut result: Vec<GateRef> = Vec::new();

            for _ in 0..shift {
                result.push(GateRef::from(Gate::ConstFalse));
            }

            if let Some(const_digit) = get_constant(digit.clone()) {
                if const_digit {
                    for g in left_operand {
                        result.push(g.clone());
                    }
                } else {
                    for _ in left_operand {
                        result.push(GateRef::from(Gate::ConstFalse));
                    }
                }
            } else {
                for g in left_operand {
                    if let Some(const_g) = get_constant((*g).clone()) {
                        if const_g {
                            result.push(digit.clone());
                        } else {
                            result.push(GateRef::from(Gate::ConstFalse));
                        }
                    } else {
                        result.push(GateRef::from(Gate::And {
                            left: g.clone(),
                            right: digit.clone(),
                        }));
                    }
                }
            }

            result
        }

        fn add_front_zeros_padding(bits: &mut Vec<GateRef>, expected_max_size: usize) {
            while bits.len() < expected_max_size {
                bits.push(GateRef::from(Gate::ConstFalse));
            }
        }

        // main algorithm for multiplication
        let expected_max_size = 2 * left.len() - 1;
        let mut replacement: Vec<GateRef> = Vec::new();

        for _ in 0..expected_max_size {
            replacement.push(GateRef::from(Gate::ConstFalse));
        }
        for (i, digit) in right.iter().enumerate() {
            let mut temp_result = mutiply_by_digit(left, digit, i);

            add_front_zeros_padding(&mut temp_result, expected_max_size);
            replacement = self.bitwise_add(&replacement, &temp_result, false);
        }

        replacement[..right.len()].to_vec()
    }

    fn divide(
        &mut self,
        dividend: &[GateRef],
        divisor: &[GateRef],
    ) -> (Vec<GateRef>, Vec<GateRef>) {
        // check if division can be done at word level
        if get_non_constant_gate(dividend).is_none() && get_non_constant_gate(divisor).is_none() {
            let const_dividend = get_numeric_from_gates(dividend);
            let const_divisor = get_numeric_from_gates(divisor);

            let quotient = get_gates_from_numeric(const_dividend / const_divisor, &dividend.len());
            let remainder = get_gates_from_numeric(const_dividend % const_divisor, &dividend.len());
            (quotient, remainder)
        } else {
            let mut quotient: Vec<GateRef> = Vec::new();
            let mut remainder: Vec<GateRef> = Vec::new();

            for i in 0..divisor.len() {
                let name = format!("quotient[bit={}]", i);
                quotient.push(GateRef::from(Gate::InputBit { name }));
                let name = format!("remainder[bit={}]", i);
                remainder.push(GateRef::from(Gate::InputBit { name }));
            }

            let temp_mul = self.bitwise_multiplication(&quotient, divisor);
            let temp_sum = self.bitwise_add(&temp_mul, &remainder, true);

            assert!(dividend.len() == temp_sum.len());

            for (left, right) in dividend.iter().zip(temp_sum.iter()) {
                let gate = xnor_gate(None, None, &*left, &*right);
                self.record_constraint(&gate, true);
            }

            (quotient, remainder)
        }
    }

    fn get_address_index(&mut self, address: &u64) -> u64 {
        let size_data = (self.model.data_range.end - self.model.data_range.start) / self.word_size;
        let size_heap = (self.model.heap_range.end - self.model.heap_range.start) / self.word_size;

        if self.model.data_range.contains(address) {
            (*address - self.model.data_range.start) / self.word_size
        } else if self.model.heap_range.contains(address) {
            size_data + (*address - self.model.heap_range.start) / self.word_size
        } else if self.model.stack_range.contains(address) {
            size_data + size_heap + (*address - self.model.stack_range.start) / self.word_size
        } else {
            warn!(
                "WARNING! trying to access address {} in memory that is undefined",
                address
            );
            u64::MAX
        }
    }

    fn record_mapping(&mut self, node: &NodeRef, replacement: Vec<GateRef>) -> Vec<GateRef> {
        let key = HashableNodeRef::from(node.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement.clone());
        replacement
    }

    fn record_mapping_adders(&mut self, gate: &GateRef, value: &GateRef) {
        let key = HashableGateRef::from(gate.clone());

        if let std::collections::hash_map::Entry::Vacant(e) = self.mapping_adders.entry(key) {
            e.insert(value.clone());
        } else {
            panic!("Trying to set constraint, but constraint already exists")
        }
    }

    fn record_constraint(&mut self, gate: &GateRef, value: bool) {
        let key = HashableGateRef::from(gate.clone());

        if let std::collections::hash_map::Entry::Vacant(e) = self.constraints.entry(key) {
            e.insert(value);
        } else {
            panic!("Trying to set constraint, but constraint already exists")
        }
    }

    fn query_existence(&mut self, node: &NodeRef) -> Option<Vec<GateRef>> {
        let key = HashableNodeRef::from(node.clone());
        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned()
        } else {
            None
        }
    }

    fn visit(&mut self, node: &NodeRef) -> Vec<GateRef> {
        let key = HashableNodeRef::from(node.clone());
        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned().unwrap()
        } else {
            assert!(!self.mapping.contains_key(&key));
            let replacement = self.process(node);
            assert!(self.mapping.contains_key(&key));
            replacement
        }
    }

    fn process(&mut self, node: &NodeRef) -> Vec<GateRef> {
        if let Some(replacement) = self.query_existence(node) {
            return replacement;
        }
        match &*node.borrow() {
            Node::Const { nid, sort, imm } => {
                let replacement = get_replacement_from_constant(sort, *imm);
                assert!(replacement.len() == sort.bitsize());
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::State {
                init: None,
                sort,
                name,
                nid,
            } => {
                // this is an "input", handle accordingly
                let mut replacement: Vec<GateRef> = Vec::new();
                let name = name.as_deref().unwrap_or("?");
                for i in 0..sort.bitsize() {
                    let name = format!("{}[bit={}]", name, i);
                    replacement.push(GateRef::from(Gate::InputBit { name }));
                }
                self.input_gates.push((node.clone(), replacement.clone()));
                assert!(replacement.len() == sort.bitsize());
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Input { nid, sort, name } => {
                let mut replacement: Vec<GateRef> = Vec::new();
                for i in 0..sort.bitsize() {
                    let name = format!("{}[bit={}]", name, i);
                    replacement.push(GateRef::from(Gate::InputBit { name }));
                }
                self.input_gates.push((node.clone(), replacement.clone()));
                assert!(replacement.len() == sort.bitsize());
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::State {
                nid: _,
                sort,
                init,
                name: _,
            } => {
                info!("normal state");
                let mut replacement = Vec::new();
                if let Some(value) = init {
                    replacement = self.visit(value);
                } else {
                    for _ in 0..sort.bitsize() {
                        replacement.push(GateRef::from(Gate::ConstFalse));
                    }
                }
                assert!(replacement.len() == sort.bitsize());
                self.record_mapping(node, replacement)
            }
            Node::Not { nid, value } => {
                let bitvector = self.visit(value);
                let mut replacement: Vec<GateRef> = Vec::new();
                for bit in bitvector.clone() {
                    replacement.push(not_gate(bit));
                }
                assert!(replacement.len() == bitvector.len());
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Bad { nid, cond, name: _ } => {
                let replacement = self.visit(cond);
                assert!(replacement.len() == 1);
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::And { nid, left, right } => {
                let left_operand = self.visit(left);
                let right_operand = self.visit(right);
                let replacement = fold_bitwise_gate(&left_operand, &right_operand, and_gate, "AND");
                assert!(left_operand.len() == replacement.len());
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Ext { nid, from, value } => {
                let mut replacement: Vec<GateRef> = self.visit(value);
                assert!(replacement.len() == from.bitsize());
                for _ in 0..(64 - from.bitsize()) {
                    replacement.push(GateRef::from(Gate::ConstFalse));
                }
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Eq { nid, left, right } => {
                let left_operand = self.visit(left);
                let right_operand = self.visit(right);
                let temp_word = fold_bitwise_gate(&left_operand, &right_operand, xnor_gate, "XNOR");
                assert!(temp_word.len() == left_operand.len());
                let replacement = fold_word_gate(&temp_word, and_gate, "WORD-AND");
                assert!(replacement.len() == 1);
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Add { nid, left, right } => {
                let left_operand = self.visit(left);
                let right_operand = self.visit(right);
                let replacement = self.bitwise_add(&left_operand, &right_operand, false);
                assert!(left_operand.len() == replacement.len());
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Ite {
                nid,
                sort: _,
                cond,
                left,
                right,
            } => {
                let cond_operand = self.visit(cond);
                assert!(cond_operand.len() == 1);
                if let Some(cond_const) = get_constant(cond_operand[0].clone()) {
                    if cond_const {
                        let left_operand = self.visit(left);
                        self.nid_to_gates.insert(*nid, left_operand.clone());
                        self.record_mapping(node, left_operand)
                    } else {
                        let right_operand = self.visit(right);
                        self.nid_to_gates.insert(*nid, right_operand.clone());
                        self.record_mapping(node, right_operand)
                    }
                } else {
                    let left_operand = self.visit(left);
                    let right_operand = self.visit(right);
                    assert!(left_operand.len() == right_operand.len());

                    let mut replacement: Vec<GateRef> = Vec::new();
                    for i in 0..left_operand.len() {
                        let left_bit = get_constant(left_operand[i].clone());
                        let right_bit = get_constant(right_operand[i].clone());

                        if are_both_constants(left_bit, right_bit) {
                            let const_true_bit = get_constant(left_operand[i].clone()).unwrap();
                            let const_false_bit = get_constant(right_operand[i].clone()).unwrap();

                            if const_true_bit == const_false_bit {
                                replacement.push(left_operand[i].clone());
                            } else if const_true_bit {
                                replacement.push(cond_operand[0].clone());
                            } else {
                                replacement.push(GateRef::from(Gate::Not {
                                    value: cond_operand[0].clone(),
                                }));
                            }
                        } else {
                            let true_bit: GateRef;
                            let false_bit: GateRef;

                            if let Some(const_true) = get_constant(left_operand[i].clone()) {
                                if const_true {
                                    true_bit = cond_operand[0].clone();
                                } else {
                                    true_bit = GateRef::from(Gate::ConstFalse);
                                }
                            } else {
                                true_bit = GateRef::from(Gate::And {
                                    left: left_operand[i].clone(),
                                    right: cond_operand[0].clone(),
                                });
                            }

                            if let Some(const_false) = get_constant(right_operand[i].clone()) {
                                if const_false {
                                    false_bit = GateRef::from(Gate::Not {
                                        value: cond_operand[0].clone(),
                                    });
                                } else {
                                    false_bit = GateRef::from(Gate::ConstFalse);
                                }
                            } else {
                                false_bit = GateRef::from(Gate::Matriarch1 {
                                    cond: cond_operand[0].clone(),
                                    right: right_operand[i].clone(),
                                });
                            }

                            let true_bit_const = get_constant(true_bit.clone());
                            let false_bit_const = get_constant(false_bit.clone());
                            replacement.push(or_gate(
                                true_bit_const,
                                false_bit_const,
                                &true_bit,
                                &false_bit,
                            ));
                        }
                    }
                    self.nid_to_gates.insert(*nid, replacement.clone());
                    self.record_mapping(node, replacement)
                }
            }
            Node::Sub { nid, left, right } => {
                let left_operand = self.visit(left);
                let right_operand = self.visit(right);

                let replacement: Vec<GateRef> =
                    self.bitwise_substraction(left_operand, right_operand);
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Ult { nid, left, right } => {
                let mut left_operand = self.visit(left);
                let mut right_operand = self.visit(right);
                left_operand.push(GateRef::from(Gate::ConstFalse));
                right_operand.push(GateRef::from(Gate::ConstFalse));

                let substracted_bitvectors = self.bitwise_substraction(left_operand, right_operand);

                if let Some(last_element) = substracted_bitvectors.last() {
                    let replacement: Vec<GateRef> = vec![(*last_element).clone()];
                    self.nid_to_gates.insert(*nid, replacement.clone());
                    self.record_mapping(node, replacement)
                } else {
                    panic!("Error in ULT, cant get MSB!")
                }
            }
            Node::Mul { nid, left, right } => {
                let left_operand = self.visit(left);
                let right_operand = self.visit(right);
                let replacement = self.bitwise_multiplication(&left_operand, &right_operand);
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Div { nid, left, right } => {
                let left_operand = self.visit(left);
                let right_operand = self.visit(right);
                let replacement = self.divide(&left_operand, &right_operand).0;
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Rem { nid, left, right } => {
                let left_operand = self.visit(left);
                let right_operand = self.visit(right);
                let replacement = self.divide(&left_operand, &right_operand).1;
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Read {
                nid,
                memory,
                address,
            } => {
                let mut replacement: Vec<GateRef> = Vec::new();
                let memory_unfolded = self.visit(memory);
                let address_unfolded = self.visit(address);
                if get_non_constant_gate(&address_unfolded).is_none() {
                    // address is constant
                    let num_address = get_numeric_from_gates(&address_unfolded);
                    let index_address = self.get_address_index(&num_address);

                    if index_address != u64::MAX {
                        let begin = (index_address * self.word_size) as usize;
                        let end = (index_address * self.word_size + self.word_size) as usize;

                        replacement = memory_unfolded[begin..end].to_vec();
                    } else {
                        for _ in 0..self.word_size {
                            replacement.push(GateRef::from(Gate::ConstFalse));
                        }
                    }
                } else {
                    let mut replacement: Vec<GateRef> = Vec::new();

                    for _ in 0..self.word_size {
                        replacement.push(GateRef::from(Gate::ConstFalse));
                    }

                    for (i, address) in self.addresses_gates.iter().enumerate() {
                        let is_equal = bitwise_equal(address, &address_unfolded)[0].clone();
                        let mut temp_word: Vec<GateRef> = Vec::new();

                        for bit_index in 0..self.word_size {
                            let current_bit = &memory_unfolded
                                [i * (self.word_size as usize) + (bit_index as usize)];

                            let const_current_bit = get_constant(current_bit.clone());
                            let const_is_equal = get_constant(is_equal.clone());

                            temp_word.push(and_gate(
                                const_current_bit,
                                const_is_equal,
                                current_bit,
                                &is_equal,
                            ));
                        }

                        replacement = fold_bitwise_gate(&replacement, &temp_word, or_gate, "OR");
                    }
                }
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            Node::Write {
                nid,
                memory,
                address,
                value,
            } => {
                let mut replacement: Vec<GateRef> = Vec::new();
                let memory_unfolded = self.visit(memory);
                let address_unfolded = self.visit(address);
                let value_unfolded = self.visit(value);

                if get_non_constant_gate(&address_unfolded).is_none() {
                    // address is constant
                    let num_address = get_numeric_from_gates(&address_unfolded);
                    let index_address = self.get_address_index(&num_address);

                    if index_address != u64::MAX {
                        let mut current_index = 0;

                        for (i, bit) in memory_unfolded.iter().enumerate() {
                            if i > 0 && i % (self.word_size as usize) == 0 {
                                current_index += 1;
                            }

                            if current_index == index_address {
                                replacement
                                    .push(value_unfolded[i % (self.word_size as usize)].clone());
                            } else {
                                replacement.push((*bit).clone());
                            }
                        }
                    } else {
                        replacement = memory_unfolded;
                    }
                } else {
                    let word_size = self.word_size as usize;
                    for (i, address) in self.addresses_gates.iter().enumerate() {
                        let is_equal = &bitwise_equal(address, &address_unfolded)[0];

                        for bit_index in 0..word_size {
                            let prev_bit = &memory_unfolded[i * word_size + bit_index];

                            let actual_bit = &value_unfolded[bit_index];

                            if let Some(const_is_equal) = get_constant(is_equal.clone()) {
                                if const_is_equal {
                                    replacement.push(actual_bit.clone());
                                } else {
                                    replacement.push(prev_bit.clone());
                                }
                            } else {
                                let const_prev_bit = get_constant(prev_bit.clone());
                                let const_actual_bit = get_constant(actual_bit.clone());

                                if are_both_constants(const_prev_bit, const_actual_bit) {
                                    if const_prev_bit.unwrap() == const_actual_bit.unwrap() {
                                        if const_prev_bit.unwrap() {
                                            replacement.push(GateRef::from(Gate::ConstTrue));
                                        } else {
                                            replacement.push(GateRef::from(Gate::ConstFalse));
                                        }
                                    } else if const_actual_bit.unwrap() {
                                        // both bits of memory are different
                                        // actual value to write == 1, prev_memory_bit == 0
                                        replacement.push((*is_equal).clone());
                                    } else {
                                        // both bits of memory are different
                                        // actual value to write == 0, prev_memory_bit == 1
                                        replacement.push(GateRef::from(Gate::Not {
                                            value: (*is_equal).clone(),
                                        }));
                                    }
                                } else {
                                    let const_is_equal = get_constant((*is_equal).clone());
                                    let temp_actual_bit = and_gate(
                                        const_prev_bit,
                                        const_is_equal,
                                        prev_bit,
                                        is_equal,
                                    );
                                    let temp_prev_bit = matriarch1_gate(
                                        const_prev_bit,
                                        const_is_equal,
                                        prev_bit,
                                        is_equal,
                                    );

                                    let const_temp_actual_bit =
                                        get_constant(temp_actual_bit.clone());
                                    let const_temp_prev_bit = get_constant(temp_prev_bit.clone());

                                    replacement.push(or_gate(
                                        const_temp_actual_bit,
                                        const_temp_prev_bit,
                                        &temp_actual_bit,
                                        &temp_prev_bit,
                                    ))
                                }
                            }
                        }
                    }
                }
                self.nid_to_gates.insert(*nid, replacement.clone());
                self.record_mapping(node, replacement)
            }
            _ => {
                panic!("this should not be happening!");
            }
        }
    }

    pub fn process_model(&mut self, model: &Model) -> Vec<GateRef> {
        // returns bad state bits
        let mut bad_state_gates: Vec<GateRef> = Vec::new();
        info!("initial bad {}", model.bad_states_initial.len());
        for node in &model.bad_states_initial {
            let bitblasted_bad_state = self.process(node);
            bad_state_gates.push(bitblasted_bad_state[0].clone());

            let key = HashableGateRef::from(bitblasted_bad_state[0].clone());
            self.gates_to_bad_nids.insert(key, node.clone());
        }

        bad_state_gates
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn constants_checking() {
        let v = "v".to_string();
        assert!(is_constant(GateRef::from(Gate::ConstTrue)));
        assert!(is_constant(GateRef::from(Gate::ConstFalse)));
        assert!(!is_constant(GateRef::from(Gate::InputBit { name: v })));
    }

    #[test]
    #[should_panic]
    fn get_constant_bit_from_non_constant() {
        get_gate_from_constant_bit(3);
    }

    #[test]
    fn get_constant_from_bit() {
        assert!(get_gate_from_constant_bit(0) == GateRef::from(Gate::ConstFalse));
        assert!(get_gate_from_constant_bit(1) == GateRef::from(Gate::ConstTrue));
    }

    #[test]
    fn get_constant_from_gate() {
        let v = "v".to_string();
        assert!(get_constant(GateRef::from(Gate::ConstFalse)) == Some(false));
        assert!(get_constant(GateRef::from(Gate::ConstTrue)) == Some(true));
        assert!(get_constant(GateRef::from(Gate::InputBit { name: v })) == None);
    }

    #[test]
    fn t_get_numeric_from_gate() {
        let v = "v".to_string();
        assert!(get_numeric_from_gate(&GateRef::from(Gate::ConstFalse)) == Some(0));
        assert!(get_numeric_from_gate(&GateRef::from(Gate::ConstTrue)) == Some(1));
        assert!(get_numeric_from_gate(&GateRef::from(Gate::InputBit { name: v })) == None);
    }

    #[test]
    fn numeric_to_gates_and_gates_to_numeric() {
        let mut num: u64 = 0;
        let mut gates = get_gates_from_numeric(num, &64);
        assert!(gates.len() == 64);
        assert!(get_numeric_from_gates(&gates) == num);

        num = 1032;
        gates = get_gates_from_numeric(num, &64);
        assert!(gates.len() == 64);
        assert!(get_numeric_from_gates(&gates) == num);

        num = 14331;
        gates = get_gates_from_numeric(num, &64);
        assert!(gates.len() == 64);
        assert!(get_numeric_from_gates(&gates) == num);
    }

    #[test]
    fn t_get_gate_from_boolean() {
        assert!(get_gate_from_boolean(true) == GateRef::from(Gate::ConstTrue));
        assert!(get_gate_from_boolean(false) == GateRef::from(Gate::ConstFalse));
    }

    #[test]
    fn t_are_there_false_constants() {
        assert!(are_there_false_constants(Some(false), Some(false)));
        assert!(are_there_false_constants(Some(false), Some(true)));
        assert!(are_there_false_constants(Some(true), Some(false)));
        assert!(!are_there_false_constants(Some(true), Some(true)));
        assert!(are_there_false_constants(None, Some(false)));
        assert!(are_there_false_constants(Some(false), None));
        assert!(!are_there_false_constants(Some(true), None));
        assert!(!are_there_false_constants(None, Some(true)));
        assert!(!are_there_false_constants(None, None));
    }

    #[test]
    fn t_are_there_true_constants() {
        assert!(!are_there_true_constants(Some(false), Some(false)));
        assert!(are_there_true_constants(Some(false), Some(true)));
        assert!(are_there_true_constants(Some(true), Some(false)));
        assert!(are_there_true_constants(Some(true), Some(true)));
        assert!(!are_there_true_constants(None, Some(false)));
        assert!(!are_there_true_constants(Some(false), None));
        assert!(are_there_true_constants(Some(true), None));
        assert!(are_there_true_constants(None, Some(true)));
        assert!(!are_there_true_constants(None, None));
    }

    #[test]
    fn t_are_both_constants() {
        assert!(are_both_constants(Some(false), Some(true)));
        assert!(are_both_constants(Some(true), Some(false)));
        assert!(are_both_constants(Some(true), Some(true)));
        assert!(are_both_constants(Some(false), Some(false)));
        assert!(!are_both_constants(None, Some(false)));
        assert!(!are_both_constants(Some(true), None));
        assert!(!are_both_constants(None, None));
    }

    #[test]
    fn t_get_non_constant_gate() {
        let mut gates: Vec<GateRef> = Vec::new();

        assert!(get_non_constant_gate(&gates).is_none());

        for i in 0..10 {
            if i % 2 == 0 {
                gates.push(GateRef::from(Gate::ConstFalse));
            } else {
                gates.push(GateRef::from(Gate::ConstTrue));
            }
        }

        assert!(get_non_constant_gate(&gates).is_none());

        let v = "v".to_string();
        gates.push(GateRef::from(Gate::InputBit { name: v }));

        let v = "v".to_string();
        assert!(
            get_non_constant_gate(&gates).unwrap() == GateRef::from(Gate::InputBit { name: v })
        );
    }

    #[test]
    fn t_get_replacement_from_constant() {
        for num in 0..10 {
            let mut sort: NodeType = NodeType::Word;
            let mut replacement = get_replacement_from_constant(&sort, num);
            assert!(replacement.len() == sort.bitsize());
            assert!(get_numeric_from_gates(&replacement) == num);

            sort = NodeType::Input1Byte;
            replacement = get_replacement_from_constant(&sort, num);
            assert!(replacement.len() == sort.bitsize());
            assert!(get_numeric_from_gates(&replacement) == num);
        }
    }

    #[test]
    fn t_and_gate() {
        let v1 = "v1".to_string();
        let v2 = "v2".to_string();
        let const_false = GateRef::from(Gate::ConstFalse);
        let const_true = GateRef::from(Gate::ConstTrue);
        let var = GateRef::from(Gate::InputBit { name: v1 });
        let var2 = GateRef::from(Gate::InputBit { name: v2 });

        assert!(and_gate(Some(true), Some(true), &const_true, &const_true) == const_true);
        assert!(and_gate(Some(false), Some(true), &const_false, &const_true) == const_false);
        assert!(and_gate(Some(false), None, &const_true, &var) == const_false);
        assert!(and_gate(Some(true), None, &const_true, &var) == var);
        info!("{:?}", and_gate(None, None, &var, &var2));
        assert!(
            and_gate(None, None, &var, &var2)
                == GateRef::from(Gate::And {
                    left: var,
                    right: var2
                })
        );
    }

    #[test]
    #[should_panic]
    fn t_and_gate2() {
        and_gate(
            Some(true),
            Some(false),
            &GateRef::from(Gate::ConstFalse),
            &GateRef::from(Gate::ConstFalse),
        );
    }

    #[test]
    fn t_matriach1_gate() {
        let v1 = "v1".to_string();
        let v2 = "v2".to_string();
        let const_false = GateRef::from(Gate::ConstFalse);
        let const_true = GateRef::from(Gate::ConstTrue);
        let var = GateRef::from(Gate::InputBit { name: v1 });
        let var2 = GateRef::from(Gate::InputBit { name: v2 });

        assert!(matriarch1_gate(Some(true), Some(true), &const_true, &const_true) == const_false);
        assert!(matriarch1_gate(Some(false), Some(true), &const_false, &const_true) == const_true);

        assert!(matriarch1_gate(Some(false), None, &const_false, &var) == var);
        assert!(matriarch1_gate(Some(true), None, &const_true, &var) == const_false);

        assert!(
            matriarch1_gate(None, None, &var2, &var)
                == GateRef::from(Gate::Matriarch1 {
                    cond: var2,
                    right: var
                })
        );
    }

    #[test]
    fn t_or_gate() {
        let v1 = "v1".to_string();
        let v2 = "v2".to_string();
        let const_false = GateRef::from(Gate::ConstFalse);
        let const_true = GateRef::from(Gate::ConstTrue);
        let var = GateRef::from(Gate::InputBit { name: v1 });
        let var2 = GateRef::from(Gate::InputBit { name: v2 });

        assert!(or_gate(Some(true), Some(true), &const_true, &const_true) == const_true);
        assert!(or_gate(Some(true), Some(false), &const_true, &const_false) == const_true);
        assert!(or_gate(Some(false), Some(true), &const_false, &const_true) == const_true);
        assert!(or_gate(Some(false), Some(false), &const_false, &const_false) == const_false);

        assert!(or_gate(None, Some(true), &var, &const_true) == const_true);
        assert!(or_gate(Some(true), None, &const_true, &var) == const_true);

        assert!(or_gate(Some(false), None, &const_false, &var) == var);
        assert!(or_gate(None, Some(false), &var, &const_false) == var);

        assert!(
            or_gate(None, None, &var, &var2)
                == GateRef::from(Gate::Or {
                    left: var,
                    right: var2
                })
        );
    }

    #[test]
    fn t_not_gate() {
        let v = "v".to_string();
        let const_false = GateRef::from(Gate::ConstFalse);
        let const_true = GateRef::from(Gate::ConstTrue);
        let var = GateRef::from(Gate::InputBit { name: v });

        assert!(not_gate(const_false.clone()) == const_true);
        assert!(not_gate(const_true) == const_false);

        assert!(not_gate(var.clone()) == GateRef::from(Gate::Not { value: var }));
    }

    #[test]
    fn t_xnor_gate() {
        let v1 = "v1".to_string();
        let v2 = "v2".to_string();
        let const_false = GateRef::from(Gate::ConstFalse);
        let const_true = GateRef::from(Gate::ConstTrue);
        let var = GateRef::from(Gate::InputBit { name: v1 });
        let var2 = GateRef::from(Gate::InputBit { name: v2 });

        assert!(xnor_gate(Some(true), Some(true), &const_true, &const_true) == const_true);
        assert!(xnor_gate(Some(true), Some(false), &const_true, &const_false) == const_false);
        assert!(xnor_gate(Some(false), Some(true), &const_false, &const_true) == const_false);
        assert!(xnor_gate(Some(false), Some(false), &const_false, &const_false) == const_true);

        assert!(xnor_gate(None, Some(true), &var, &const_true) == var);
        assert!(xnor_gate(Some(true), None, &const_true, &var) == var);

        assert!(
            xnor_gate(Some(false), None, &const_false, &var)
                == GateRef::from(Gate::Not { value: var.clone() })
        );

        let result = xnor_gate(None, None, &var, &var2);
        assert!(result != GateRef::from(Gate::Not { value: var }));
        assert!(result != GateRef::from(Gate::Not { value: var2 }));
        assert!(result != const_true);
        assert!(result != const_false);
    }

    #[test]
    fn t_are_there_2_constants() {
        let v = "v".to_string();
        let const_false = GateRef::from(Gate::ConstFalse);
        let const_true = GateRef::from(Gate::ConstTrue);
        let var = GateRef::from(Gate::InputBit { name: v });
        assert!(are_there_2_constants(&const_false, &var, &const_true));
        assert!(are_there_2_constants(&const_false, &var, &const_false));

        assert!(are_there_2_constants(&const_true, &var, &const_true));
    }
}

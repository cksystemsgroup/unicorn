#![allow(dead_code)]
#![allow(clippy::many_single_char_names)]

use crate::bitvec::*;
use crate::formula_graph::{ArgumentSide, BooleanFunction, Formula, Node, NodeIndex};
use crate::ternary::*;
use petgraph::{visit::EdgeRef, Direction};
use rand::{random, Rng};
use riscv_decode::Instruction;

pub type Assignment<T> = Vec<T>;

pub trait Solver {
    fn solve(&mut self, formula: &Formula, root: NodeIndex) -> Option<Vec<BitVector>>;
}

// check if invertability condition is met
fn is_invertable(
    instruction: Instruction,
    x: TernaryBitVector,
    s: BitVector,
    t: BitVector,
    d: ArgumentSide,
) -> bool {
    match instruction {
        Instruction::Add(_) | Instruction::Addi(_) => x.mcb(t - s),
        Instruction::Sub(_) => match d {
            ArgumentSide::Lhs => x.mcb(t + s),
            ArgumentSide::Rhs => x.mcb(s - t),
        },
        Instruction::Mul(_) => {
            fn y(s: BitVector, t: BitVector) -> BitVector {
                let c = s.ctz();
                (t >> c) * (s >> c).modinverse().unwrap()
            }

            ((-s | s) & t == t)
                && (s == BitVector(0) || (!s.odd() || x.mcb(t * s.modinverse().unwrap())))
                && (s.odd() || (x << s.ctz()).mcb(y(s, t) << s.ctz()))
        }
        _ => unimplemented!(),
    }
}

fn is_constraint_invertable(
    bf: BooleanFunction,
    _x: TernaryBitVector,
    _s: BitVector,
    _t: BitVector,
    _d: ArgumentSide,
) -> bool {
    match bf {
        BooleanFunction::Equals => true,
        BooleanFunction::NotEqual => true,
        _ => unimplemented!(),
    }
}

fn is_consistent(instruction: Instruction, x: TernaryBitVector, t: BitVector) -> bool {
    match instruction {
        Instruction::Add(_) | Instruction::Addi(_) | Instruction::Sub(_) => true,
        Instruction::Mul(_) => {
            fn value_exists(x: TernaryBitVector, t: BitVector) -> bool {
                let y = x.constant_bits() | (BitVector::ones() & !x.constant_bit_mask());

                x.mcb(y) && t.ctz() >= y.ctz()
            }

            (!(t != BitVector(0)) || (x.1 != BitVector(0)))
                && (!t.odd() || (x.1.lsb() != 0))
                && (t.odd() || value_exists(x, t))
        }
        _ => unimplemented!(),
    }
}

fn is_leaf(formula: &Formula, idx: NodeIndex) -> bool {
    let incoming = formula.edges_directed(idx, Direction::Incoming).count();

    incoming == 0
}

// this computation is a tough problem.
// the original authors did this by using bit blasting to AIG and optimizations (performance
// implication is huge).
// but there are other approaches not tested by the authors.
// for now we do not use constant bits (optimization) and therefore create fully undetermined bit
// vectors only.
fn compute_at(formula: &Formula) -> Assignment<TernaryBitVector> {
    formula
        .node_indices()
        .map(|_| TernaryBitVector(BitVector(0), BitVector::ones()))
        .collect::<Assignment<TernaryBitVector>>()
}

// initialize bit vectors with a consistent intial assignment to the formula
// inputs are initialized with random values
fn initialize_ab(formula: &Formula) -> Assignment<BitVector> {
    // Initialize values for all input/const nodes
    let mut ab = formula
        .node_indices()
        .map(|i| match formula[i] {
            Node::Constant(c) => BitVector(c.value),
            _ => BitVector(random::<u64>()),
        })
        .collect::<Assignment<BitVector>>();

    // Propagate all values down when all input/const nodes are initialized
    formula.node_indices().for_each(|i| match formula[i] {
        Node::Input(_) | Node::Constant(_) => {
            formula
                .neighbors_directed(i, Direction::Outgoing)
                .for_each(|n| propagate_assignment(formula, &mut ab, n));
        }
        _ => {}
    });

    ab
}

// selects a child node to propagate downwards
// always selects an "essential" input if there is one
// otherwise selects an input undeterministically
fn select(
    f: &Formula,
    idx: NodeIndex,
    t: BitVector,
    at: &[TernaryBitVector],
    ab: &[BitVector],
) -> (NodeIndex, NodeIndex, ArgumentSide) {
    let (lhs, rhs) = parents(f, idx);

    fn is_constant(f: &Formula, n: NodeIndex) -> bool {
        matches!(f[n], Node::Constant(_))
    }

    #[allow(clippy::if_same_then_else)]
    if is_constant(f, lhs) {
        (rhs, lhs, ArgumentSide::Rhs)
    } else if is_constant(f, rhs) {
        (lhs, rhs, ArgumentSide::Lhs)
    } else if is_essential(f, lhs, ArgumentSide::Lhs, rhs, t, at, ab) {
        (lhs, rhs, ArgumentSide::Lhs)
    } else if is_essential(f, rhs, ArgumentSide::Rhs, lhs, t, at, ab) {
        (rhs, lhs, ArgumentSide::Rhs)
    } else if random() {
        (rhs, lhs, ArgumentSide::Rhs)
    } else {
        (lhs, rhs, ArgumentSide::Lhs)
    }
}

fn compute_inverse_value(
    i: Instruction,
    x: TernaryBitVector,
    s: BitVector,
    t: BitVector,
    d: ArgumentSide,
) -> BitVector {
    match i {
        Instruction::Add(_) | Instruction::Addi(_) => t - s,
        Instruction::Sub(_) => match d {
            ArgumentSide::Lhs => t + s,
            ArgumentSide::Rhs => s - t,
        },
        Instruction::Mul(_) => {
            let y = s >> s.ctz();

            let y_inv = y.modinverse().unwrap();

            let result = (t >> s.ctz()) * y_inv;

            let to_shift = 64 - s.ctz();

            let arbitrary_bit_mask = if to_shift == 64 {
                BitVector(0)
            } else {
                BitVector::ones() << to_shift
            };

            let arbitrary_bits = BitVector(random::<u64>()) & arbitrary_bit_mask;

            let result_with_arbitrary = result | arbitrary_bits;

            (result_with_arbitrary & !x.constant_bit_mask()) | x.constant_bits()
        }
        _ => unimplemented!(),
    }
}

fn random_from(r: std::ops::Range<u64>) -> u64 {
    let lowest = r.start as f64;
    let highest = (r.end - r.start) as f64;

    (lowest + random::<f64>() * highest) as u64
}

fn compute_consistent_value(
    i: Instruction,
    _x: TernaryBitVector,
    _s: BitVector,
    t: BitVector,
    _d: ArgumentSide,
) -> BitVector {
    match i {
        Instruction::Add(_) | Instruction::Addi(_) | Instruction::Sub(_) => {
            BitVector(random::<u64>())
        }
        Instruction::Mul(_) => BitVector({
            if t == BitVector(0) {
                0
            } else {
                let mut r;
                loop {
                    r = random::<u128>();
                    if r != 0 {
                        break;
                    }
                }
                if t.ctz() < r.trailing_zeros() {
                    r >>= r.trailing_zeros() - t.ctz();
                }
                assert!(t.ctz() >= r.trailing_zeros());
                r as u64
            }
        }),
        _ => unimplemented!(),
    }
}

fn compute_inverse_constraint_value(
    bf: BooleanFunction,
    _x: TernaryBitVector,
    s: BitVector,
    _t: BitVector,
    _d: ArgumentSide,
) -> BitVector {
    match bf {
        BooleanFunction::Equals => s,
        BooleanFunction::NotEqual => loop {
            let r = BitVector(random::<u64>());

            if r != s {
                return r;
            }
        },
        _ => unimplemented!(),
    }
}

const CHOOSE_INVERSE: f64 = 0.90;

// computes an inverse/consistent target value
#[allow(clippy::too_many_arguments)]
fn value(
    f: &Formula,
    n: NodeIndex,
    nx: NodeIndex,
    ns: NodeIndex,
    side: ArgumentSide,
    t: BitVector,
    at: &[TernaryBitVector],
    ab: &[BitVector],
) -> BitVector {
    let x = at[nx.index()];
    let s = ab[ns.index()];

    match &f[n] {
        Node::Instruction(i) => {
            let consistent = compute_consistent_value(i.instruction, x, s, t, side);

            if is_invertable(i.instruction, x, s, t, side) {
                let inverse = compute_inverse_value(i.instruction, x, s, t, side);
                let choose_inverse =
                    rand::thread_rng().gen_range(0.0_f64, 1.0_f64) < CHOOSE_INVERSE;

                if choose_inverse {
                    inverse
                } else {
                    consistent
                }
            } else {
                consistent
            }
        }
        Node::Constraint(c) => {
            if is_constraint_invertable(c.op, x, s, t, side) {
                compute_inverse_constraint_value(c.op, x, s, t, side)
            // TODO: Compute consistent value and choose between inverse and consistent
            // non-deterministiclly
            //let consistent = compute_consistent_value()
            } else {
                unimplemented!()
            }
        }
        _ => unimplemented!(),
    }
}

fn is_essential(
    formula: &Formula,
    this: NodeIndex,
    on_side: ArgumentSide,
    other: NodeIndex,
    t: BitVector,
    at: &[TernaryBitVector],
    ab: &[BitVector],
) -> bool {
    let at_ns = at[other.index()];
    let ab_nx = ab[this.index()];

    match &formula[other] {
        Node::Instruction(i) => !is_invertable(i.instruction, at_ns, ab_nx, t, on_side.other()),
        Node::Constraint(c) => !is_constraint_invertable(c.op, at_ns, ab_nx, t, on_side.other()),
        // TODO: not mentioned in paper => improvised. is that really true?
        Node::Constant(_) | Node::Input(_) => false,
    }
}

pub fn parents(f: &Formula, n: NodeIndex) -> (NodeIndex, NodeIndex) {
    fn target_by_side(f: &Formula, n: NodeIndex, side: ArgumentSide) -> NodeIndex {
        f.edges_directed(n, Direction::Incoming)
            .find(|e| *e.weight() == side)
            .unwrap()
            .source()
    }

    let lhs = target_by_side(f, n, ArgumentSide::Lhs);
    let rhs = target_by_side(f, n, ArgumentSide::Rhs);

    (lhs, rhs)
}

fn update_assignment(f: &Formula, ab: &mut Assignment<BitVector>, n: NodeIndex, v: BitVector) {
    ab[n.index()] = v;

    f.neighbors_directed(n, Direction::Outgoing)
        .for_each(|n| propagate_assignment(f, ab, n));
}

fn propagate_assignment(f: &Formula, ab: &mut Assignment<BitVector>, n: NodeIndex) {
    fn update_binary<Op>(f: &Formula, ab: &mut Assignment<BitVector>, n: NodeIndex, op: Op)
    where
        Op: FnOnce(BitVector, BitVector) -> BitVector,
    {
        let (lhs, rhs) = parents(f, n);

        let result = op(ab[lhs.index()], ab[rhs.index()]);

        ab[n.index()] = result;
    }

    match &f[n] {
        Node::Instruction(i) => {
            match i.instruction {
                Instruction::Add(_) | Instruction::Addi(_) => update_binary(f, ab, n, |l, r| l + r),
                Instruction::Sub(_) => update_binary(f, ab, n, |l, r| l - r),
                Instruction::Mul(_) => update_binary(f, ab, n, |l, r| l * r),
                Instruction::Sltu(_) => {
                    update_binary(f, ab, n, |l, r| BitVector(if l < r { 1 } else { 0 }))
                }
                _ => unimplemented!(),
            }
            f.neighbors_directed(n, Direction::Outgoing)
                .for_each(|n| propagate_assignment(f, ab, n));
        }
        Node::Constraint(c) => match c.op {
            BooleanFunction::Equals => {
                update_binary(
                    f,
                    ab,
                    n,
                    |l, r| {
                        if l == r {
                            BitVector(1)
                        } else {
                            BitVector(0)
                        }
                    },
                )
            }
            BooleanFunction::NotEqual => {
                update_binary(
                    f,
                    ab,
                    n,
                    |l, r| {
                        if l == r {
                            BitVector(0)
                        } else {
                            BitVector(1)
                        }
                    },
                )
            }
            bf => unimplemented!("not implemented: {:?}", bf),
        },
        _ => unreachable!(),
    }
}

// can only handle one Equals constrain with constant
fn sat(
    formula: &Formula,
    root: NodeIndex,
    at: Assignment<TernaryBitVector>,
    mut ab: Assignment<BitVector>,
) -> Assignment<BitVector> {
    while ab[root.index()] != BitVector(1) {
        let mut n = root;
        let mut t = BitVector(1);

        while !is_leaf(formula, n) {
            let (nx, ns, side) = select(formula, n, t, &at, &ab);

            match formula[n] {
                Node::Instruction(instr) => {
                    let x = at[nx.index()];
                    if !is_consistent(instr.instruction, x, t) {
                        break;
                    }
                }
                Node::Constraint(_) => {}
                _ => panic!("non instruction node found"),
            };

            let v = value(formula, n, nx, ns, side, t, &at, &ab);

            t = v;
            n = nx;
        }

        if !at[n.index()].is_const() {
            update_assignment(formula, &mut ab, n, t);
        }
    }

    ab
}

pub struct NativeSolver {}

impl Default for NativeSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeSolver {
    pub fn new() -> Self {
        Self {}
    }
}

impl Solver for NativeSolver {
    fn solve(&mut self, formula: &Formula, root: NodeIndex) -> Option<Vec<BitVector>> {
        solve(formula, root)
    }
}

pub fn solve(formula: &Formula, root: NodeIndex) -> Option<Assignment<BitVector>> {
    let ab = initialize_ab(formula);
    let at = compute_at(formula);

    let result = sat(formula, root, at, ab);

    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula_graph::{Const, Constraint, Input, Instr};
    use riscv_decode::types::*;

    fn create_formula_with_input() -> (Formula, NodeIndex) {
        let mut formula = Formula::new();

        let input = Node::Input(Input::new("x0".to_string()));
        let input_idx = formula.add_node(input);

        (formula, input_idx)
    }

    fn add_equals_constrain(
        formula: &mut Formula,
        to: NodeIndex,
        on: ArgumentSide,
        constant: u64,
    ) -> NodeIndex {
        let constrain =
            Node::Constraint(Constraint::new("exit".to_string(), BooleanFunction::Equals));
        let constrain_idx = formula.add_node(constrain);

        let constrain_c = Node::Constant(Const::new(constant));
        let constrain_c_idx = formula.add_node(constrain_c);

        formula.add_edge(to, constrain_idx, on);
        formula.add_edge(constrain_c_idx, constrain_idx, on.other());

        constrain_idx
    }

    #[test]
    fn solve_trivial_equals_constrain() {
        let (mut formula, input_idx) = create_formula_with_input();

        let root = add_equals_constrain(&mut formula, input_idx, ArgumentSide::Lhs, 10);

        let result = solve(&formula, root);

        assert!(result.is_some(), "has result for trivial equals constrain");
        assert_eq!(
            result.unwrap()[input_idx.index()],
            BitVector(10),
            "solver result of trivial equal constrain has right value"
        );
    }

    #[test]
    fn solve_bvadd() {
        let (mut formula, input_idx) = create_formula_with_input();

        let constant = Node::Constant(Const::new(3));
        let constant_idx = formula.add_node(constant);

        let instr = Node::Instruction(Instr::new(Instruction::Add(RType(0)))); // registers do not mather
        let instr_idx = formula.add_node(instr);

        formula.add_edge(input_idx, instr_idx, ArgumentSide::Lhs);
        formula.add_edge(constant_idx, instr_idx, ArgumentSide::Rhs);

        let root = add_equals_constrain(&mut formula, instr_idx, ArgumentSide::Lhs, 10);

        let result = solve(&formula, root);

        assert!(result.is_some(), "has result for trivial add op");
        assert_eq!(
            result.unwrap()[input_idx.index()],
            BitVector(7),
            "solver result of trivial add op has right value"
        );
    }

    fn instr_to_str(i: Instruction) -> &'static str {
        match i {
            Instruction::Mul(_) => "*",
            _ => unimplemented!(),
        }
    }

    fn test_invertability(
        op: Instruction,
        x: &'static str,
        s: u64,
        t: u64,
        side: ArgumentSide,
        result: bool,
        msg: &'static str,
    ) {
        let x = TernaryBitVector::lit(x);
        let s = BitVector(s);
        let t = BitVector(t);

        if side == ArgumentSide::Lhs {
            assert!(
                is_invertable(op, x, s, t, side) == result,
                "{:?} {} {:?} == {:?}   {}",
                x,
                instr_to_str(op),
                s,
                t,
                msg
            );
        } else {
            assert!(
                is_invertable(op, x, s, t, side) == result,
                "{:?} {} {:?} == {:?}   {}",
                s,
                instr_to_str(op),
                x,
                t,
                msg
            );
        }
    }

    fn test_consistence(
        op: Instruction,
        x: &'static str,
        s: u64,
        t: u64,
        result: bool,
        msg: &'static str,
    ) {
        let x = TernaryBitVector::lit(x);
        let s = BitVector(s);
        let t = BitVector(t);
        assert!(
            is_consistent(op, x, t) == result,
            "{:?} {} {:?} == {:?}   {}",
            x,
            instr_to_str(op),
            s,
            t,
            msg
        );
    }

    fn test_inverse_value_computation<F>(
        op: Instruction,
        x: &'static str,
        s: u64,
        t: u64,
        d: ArgumentSide,
        f: F,
    ) where
        F: FnOnce(BitVector, BitVector) -> BitVector,
    {
        let x = TernaryBitVector::lit(x);
        let s = BitVector(s);
        let t = BitVector(t);

        let computed = compute_inverse_value(op, x, s, t, d);

        // prove: computed <> s == t        where <> is the binary operator
        assert_eq!(
            f(computed, s),
            t,
            "{:?} {} {:?} == {:?}",
            computed,
            instr_to_str(op),
            s,
            t
        );
    }

    fn test_consistent_value_computation<F>(
        op: Instruction,
        x: &'static str,
        s: u64,
        t: u64,
        d: ArgumentSide,
        f: F,
    ) where
        F: FnOnce(BitVector, BitVector) -> BitVector,
    {
        let x = TernaryBitVector::lit(x);
        let s = BitVector(s);
        let t = BitVector(t);

        let computed = compute_consistent_value(op, x, s, t, d);

        // TODO: How to test consistent values?
        // To proof that there exists a y, we would have to compute and inverse value, which is not
        // always possible.
        // I think, Alastairs
        // prove: Ey.(computed <> y == t)        where <> is the binary bit vector operator

        let y = match op {
            Instruction::Add(_) => Some(t - computed),
            _ => None,
        };

        if let Some(inverse) = y {
            if d == ArgumentSide::Lhs {
                assert_eq!(
                    f(computed, inverse),
                    t,
                    "{:?} {} {:?} == {:?}",
                    computed,
                    instr_to_str(op),
                    inverse,
                    t
                );
            } else {
                assert_eq!(
                    f(inverse, computed),
                    t,
                    "{:?} {} {:?} == {:?}",
                    inverse,
                    instr_to_str(op),
                    computed,
                    t
                );
            }
        }
    }

    // TODO: add tests for ADD
    // TODO: add tests for SUB

    const MUL: Instruction = Instruction::Mul(RType(0));

    #[test]
    fn check_invertability_condition_for_mul() {
        let side = ArgumentSide::Lhs;

        test_invertability(MUL, "1", 0b1, 0b1, side, true, "trivial multiplication");
        test_invertability(
            MUL,
            "1",
            0b10,
            0b1,
            side,
            false,
            "operand bigger than result",
        );
        test_invertability(
            MUL,
            "0*",
            0b10,
            0b10,
            side,
            true,
            "operand with undetermined bits and possible invsere",
        );
        test_invertability(
            MUL,
            "*0",
            0b10,
            0b10,
            side,
            false,
            "operand with undetermined bits and no inverse value",
        );
        test_invertability(
            MUL,
            "***",
            0b100,
            0b100,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
        test_invertability(
            MUL,
            "**0",
            0b10,
            0b1100,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
    }

    #[test]
    fn compute_inverse_values_for_mul() {
        let side = ArgumentSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            l * r
        }

        // test only for values which are actually invertable
        test_inverse_value_computation(MUL, "1", 0b1, 0b1, side, f);
        test_inverse_value_computation(MUL, "0*", 0b10, 0b10, side, f);
        test_inverse_value_computation(MUL, "***", 0b100, 0b100, side, f);
        test_inverse_value_computation(MUL, "**0", 0b10, 0b1100, side, f);
    }

    #[test]
    fn check_consistency_condition_for_mul() {
        let condition = "t != 0 => x^hi != 0";

        test_consistence(MUL, "1", 0b10, 0b110, true, condition);
        test_consistence(MUL, "0", 0b10, 0b110, false, condition);

        let condition = "odd(t) => x^hi[lsb] != 0";

        test_consistence(MUL, "*00", 0b1, 0b101, false, condition);
        test_consistence(MUL, "*01", 0b1, 0b101, true, condition);
        test_consistence(MUL, "*0*", 0b1, 0b11, true, condition);

        let condition = "Ey.(mcb(x, y) && ctz(t) >= ctz(y))";

        test_consistence(MUL, "*00", 0b1, 0b100, true, condition);
        test_consistence(MUL, "*00", 0b1, 0b10, false, condition);
    }

    #[test]
    fn compute_consistent_values_for_mul() {
        let side = ArgumentSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            l * r
        }

        // test only for values which actually have a consistent value
        test_consistent_value_computation(MUL, "1", 0b10, 0b110, side, f);
        test_consistent_value_computation(MUL, "*01", 0b1, 0b101, side, f);
        test_consistent_value_computation(MUL, "*0*", 0b1, 0b11, side, f);
        test_consistent_value_computation(MUL, "*00", 0b1, 0b100, side, f);
    }
}

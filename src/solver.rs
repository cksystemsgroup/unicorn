#![allow(clippy::many_single_char_names)]
#![allow(clippy::if_same_then_else)]
#![allow(clippy::neg_cmp_op_on_partial_ord)]

use crate::{
    bitvec::*,
    symbolic_state::{get_operands, BVOperator, Formula, Node, OperandSide, SymbolId},
};
use log::{debug, log_enabled, trace, Level};
use petgraph::{visit::EdgeRef, Direction};
use rand::{distributions::Uniform, random, thread_rng, Rng};
use std::time::{Duration, Instant};
use thiserror::Error;

pub type Assignment<T> = Vec<T>;

pub trait Solver: Default {
    fn name() -> &'static str;

    fn solve(
        &self,
        formula: &Formula,
        root: SymbolId,
    ) -> Result<Option<Assignment<BitVector>>, SolverError> {
        debug!("try to solve with {} solver", Self::name());

        time_debug!("finished solving formula", {
            self.solve_impl(formula, root)
        })
    }

    fn solve_impl(
        &self,
        formula: &Formula,
        root: SymbolId,
    ) -> Result<Option<Assignment<BitVector>>, SolverError>;
}

#[derive(Debug, Error)]
pub enum SolverError {
    #[error("failed to compute satisfiability within the given limits")]
    SatUnknown,

    #[error("could not find a satisfiable assignment before timing out")]
    Timeout,
}

pub struct MonsterSolver {}

impl Default for MonsterSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl MonsterSolver {
    pub fn new() -> Self {
        Self {}
    }
}

impl Solver for MonsterSolver {
    fn name() -> &'static str {
        "Monster"
    }

    fn solve_impl(
        &self,
        formula: &Formula,
        root: SymbolId,
    ) -> Result<Option<Assignment<BitVector>>, SolverError> {
        let ab = initialize_ab(formula);

        let timeout_time = Duration::new(3, 0);

        sat(formula, root, ab, timeout_time)
    }
}

// check if invertability condition is met
fn is_invertable(op: BVOperator, s: BitVector, t: BitVector, d: OperandSide) -> bool {
    match op {
        BVOperator::Add => true,
        BVOperator::Sub => true,
        BVOperator::Mul => (-s | s) & t == t,
        BVOperator::Divu => match d {
            OperandSide::Lhs => {
                if (t == BitVector::ones()) && s == BitVector(0) {
                    false
                } else if (t == BitVector::ones()) && (s != BitVector(0)) && (s != BitVector(1)) {
                    false
                } else if (t != BitVector::ones()) && (s == BitVector(0)) {
                    false
                } else {
                    !t.mulo(s)
                }
            }
            OperandSide::Rhs => {
                if (t == s) && (t == BitVector(0)) {
                    false
                } else if (t == BitVector(0)) && (s == BitVector::ones()) {
                    false
                } else {
                    !(s < t)
                }
            }
        },
        BVOperator::Sltu => {
            // (x<s) = t
            if d == OperandSide::Lhs {
                if t == BitVector(1) {
                    !(s == BitVector(0))
                } else {
                    true
                }
            // (s<x) = t
            } else if t == BitVector(1) {
                !(s == BitVector::ones())
            } else {
                true
            }
        }
        BVOperator::Not => true,
        BVOperator::BitwiseAnd => (t & s) == t,
        BVOperator::Equals => true,
    }
}

fn is_leaf(formula: &Formula, idx: SymbolId) -> bool {
    let incoming = formula.edges_directed(idx, Direction::Incoming).count();

    incoming == 0
}

// initialize bit vectors with a consistent intial assignment to the formula
// inputs are initialized with random values
fn initialize_ab(formula: &Formula) -> Assignment<BitVector> {
    // Initialize values for all input/const nodes
    let mut ab = formula
        .node_indices()
        .map(|i| match formula[i] {
            Node::Constant(c) => BitVector(c),
            _ => BitVector(random::<u64>()),
        })
        .collect::<Assignment<BitVector>>();

    if log_enabled!(Level::Trace) {
        formula
            .node_indices()
            .filter(|i| matches!(formula[*i], Node::Input(_)))
            .for_each(|i| {
                trace!("initialize: x{} <- {:#x}", i.index(), ab[i.index()].0);
            });
    }

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
    idx: SymbolId,
    t: BitVector,
    ab: &[BitVector],
) -> (SymbolId, SymbolId, OperandSide) {
    if let (lhs, Some(rhs)) = get_operands(f, idx) {
        fn is_constant(f: &Formula, n: SymbolId) -> bool {
            matches!(f[n], Node::Constant(_))
        }

        #[allow(clippy::if_same_then_else)]
        if is_constant(f, lhs) {
            (rhs, lhs, OperandSide::Rhs)
        } else if is_constant(f, rhs) {
            (lhs, rhs, OperandSide::Lhs)
        } else if is_essential(f, lhs, OperandSide::Lhs, rhs, t, ab) {
            (lhs, rhs, OperandSide::Lhs)
        } else if is_essential(f, rhs, OperandSide::Rhs, lhs, t, ab) {
            (rhs, lhs, OperandSide::Rhs)
        } else if random() {
            (rhs, lhs, OperandSide::Rhs)
        } else {
            (lhs, rhs, OperandSide::Lhs)
        }
    } else {
        panic!("can only select path for binary operators")
    }
}

fn compute_inverse_value(op: BVOperator, s: BitVector, t: BitVector, d: OperandSide) -> BitVector {
    match op {
        BVOperator::Add => t - s,
        BVOperator::Sub => match d {
            OperandSide::Lhs => t + s,
            OperandSide::Rhs => s - t,
        },
        BVOperator::Mul => {
            let y = s >> s.ctz();

            let y_inv = y
                .modinverse()
                .expect("a modular inverse has to exist iff operator is invertable");

            let result = (t >> s.ctz()) * y_inv;

            let to_shift = 64 - s.ctz();

            let arbitrary_bit_mask = if to_shift == 64 {
                BitVector(0)
            } else {
                BitVector::ones() << to_shift
            };

            let arbitrary_bits = BitVector(random::<u64>()) & arbitrary_bit_mask;

            result | arbitrary_bits
        }
        BVOperator::Sltu => {
            if d == OperandSide::Lhs {
                if t == BitVector(0) {
                    // x<s == false
                    // therefore we need a random x>=s
                    BitVector(thread_rng().sample(Uniform::new_inclusive(s.0, BitVector::ones().0)))
                } else {
                    // x<s == true
                    // therefore we need a random x<s
                    BitVector(thread_rng().sample(Uniform::new(0, s.0)))
                }
            } else if t == BitVector(0) {
                // s<x == false
                // therefore we need a random x<=s
                BitVector(thread_rng().sample(Uniform::new_inclusive(0, s.0)))
            } else {
                // s<x == true
                // therefore we need a random x>s
                BitVector(thread_rng().sample(Uniform::new_inclusive(s.0 + 1, BitVector::ones().0)))
            }
        }
        BVOperator::Divu => match d {
            OperandSide::Lhs => {
                if (t == BitVector::ones()) && (s == BitVector(1)) {
                    BitVector::ones()
                } else {
                    let range_start = t * s;
                    if range_start.0.overflowing_add(s.0 - 1).1 {
                        BitVector(
                            thread_rng()
                                .sample(Uniform::new_inclusive(range_start.0, u64::max_value())),
                        )
                    } else {
                        BitVector(thread_rng().sample(Uniform::new_inclusive(
                            range_start.0,
                            range_start.0 + (s.0 - 1),
                        )))
                    }
                }
            }
            OperandSide::Rhs => {
                if (t == s) && t == BitVector::ones() {
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, 1)))
                } else if (t == BitVector::ones()) && (s != BitVector::ones()) {
                    BitVector(0)
                } else {
                    s / t
                }
            }
        },
        BVOperator::BitwiseAnd => BitVector(random::<u64>()) | t,
        BVOperator::Equals => {
            if t == BitVector(0) {
                loop {
                    let r = BitVector(random::<u64>());
                    if r != s {
                        break r;
                    }
                }
            } else {
                s
            }
        }
        _ => unreachable!("unknown operator or unary operator: {:?}", op),
    }
}

fn compute_consistent_value(op: BVOperator, t: BitVector, d: OperandSide) -> BitVector {
    match op {
        BVOperator::Add | BVOperator::Sub | BVOperator::Equals => BitVector(random::<u64>()),
        BVOperator::Mul => BitVector({
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
        BVOperator::Divu => match d {
            OperandSide::Lhs => {
                if (t == BitVector::ones()) || (t == BitVector(0)) {
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, u64::max_value() - 1)))
                } else {
                    let mut y = BitVector(0);
                    while !(y != BitVector(0)) && !(y.mulo(t)) {
                        y = BitVector(
                            thread_rng().sample(Uniform::new_inclusive(0, u64::max_value())),
                        );
                    }

                    y * t
                }
            }
            OperandSide::Rhs => {
                if t == BitVector::ones() {
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, 1)))
                } else {
                    BitVector(
                        thread_rng().sample(Uniform::new_inclusive(0, u64::max_value() / t.0)),
                    )
                }
            }
        },
        BVOperator::Sltu => {
            if d == OperandSide::Lhs {
                if t == BitVector(0) {
                    // x<s == false
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, BitVector::ones().0)))
                } else {
                    // x<s == true
                    BitVector(thread_rng().sample(Uniform::new(0, BitVector::ones().0)))
                }
            } else if t == BitVector(0) {
                // s<x == false
                BitVector(thread_rng().sample(Uniform::new_inclusive(0, BitVector::ones().0)))
            } else {
                // s<x == true
                BitVector(thread_rng().sample(Uniform::new(1, BitVector::ones().0)))
            }
        }
        BVOperator::BitwiseAnd => BitVector(random::<u64>()) | t,
        _ => unreachable!("unknown operator for consistent value: {:?}", op),
    }
}

fn compute_inverse_value_for_unary_op(op: BVOperator, t: BitVector) -> BitVector {
    match op {
        BVOperator::Not => {
            if t == BitVector(0) {
                BitVector(1)
            } else {
                BitVector(0)
            }
        }
        _ => unreachable!("not unary operator: {:?}", op),
    }
}

const CHOOSE_INVERSE: f64 = 0.90;

// computes an inverse/consistent target value
#[allow(clippy::too_many_arguments)]
fn value(
    f: &Formula,
    n: SymbolId,
    ns: SymbolId,
    side: OperandSide,
    t: BitVector,
    ab: &[BitVector],
) -> BitVector {
    let s = ab[ns.index()];

    match &f[n] {
        Node::Operator(op) => {
            let consistent = compute_consistent_value(*op, t, side);

            if is_invertable(*op, s, t, side) {
                let inverse = compute_inverse_value(*op, s, t, side);
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
        _ => unimplemented!(),
    }
}

fn is_essential(
    formula: &Formula,
    this: SymbolId,
    on_side: OperandSide,
    other: SymbolId,
    t: BitVector,
    ab: &[BitVector],
) -> bool {
    let ab_nx = ab[this.index()];

    match &formula[other] {
        Node::Operator(op) => !is_invertable(*op, ab_nx, t, on_side.other()),
        // TODO: not mentioned in paper => improvised. is that really true?
        Node::Constant(_) | Node::Input(_) => false,
    }
}

fn get_operand(f: &Formula, n: SymbolId) -> SymbolId {
    f.edges_directed(n, Direction::Incoming)
        .next()
        .expect("every unary operator must have an operand")
        .source()
}

fn update_assignment(f: &Formula, ab: &mut Assignment<BitVector>, n: SymbolId, v: BitVector) {
    ab[n.index()] = v;

    assert!(
        matches!(f[n], Node::Input(_)),
        "only inputs can be assigned"
    );

    trace!("update: x{} <- {:#x}", n.index(), v.0);

    f.neighbors_directed(n, Direction::Outgoing)
        .for_each(|n| propagate_assignment(f, ab, n));
}

fn propagate_assignment(f: &Formula, ab: &mut Assignment<BitVector>, n: SymbolId) {
    fn update_binary<Op>(f: &Formula, ab: &mut Assignment<BitVector>, n: SymbolId, s: &str, op: Op)
    where
        Op: FnOnce(BitVector, BitVector) -> BitVector,
    {
        if let (lhs, Some(rhs)) = get_operands(f, n) {
            let result = op(ab[lhs.index()], ab[rhs.index()]);

            trace!(
                "propagate: x{} := x{}({:#x}) {} x{}({:#x}) |- x{} <- {:#x}",
                n.index(),
                lhs.index(),
                ab[lhs.index()].0,
                s,
                rhs.index(),
                ab[rhs.index()].0,
                n.index(),
                result.0
            );

            ab[n.index()] = result;
        } else {
            panic!("can not update binary operator with 1 operand")
        }
    }

    fn update_unary<Op>(f: &Formula, ab: &mut Assignment<BitVector>, n: SymbolId, s: &str, op: Op)
    where
        Op: FnOnce(BitVector) -> BitVector,
    {
        if let (p, None) = get_operands(f, n) {
            let result = op(ab[p.index()]);

            trace!(
                "propagate: x{} := {}x{}({:#x}) |- x{} <- {:#x}",
                n.index(),
                s,
                p.index(),
                ab[p.index()].0,
                n.index(),
                result.0
            );

            ab[n.index()] = result;
        } else {
            panic!("can not update unary operator with more than one operand")
        }
    }

    match &f[n] {
        Node::Operator(op) => {
            match op {
                BVOperator::Add => update_binary(f, ab, n, "+", |l, r| l + r),
                BVOperator::Sub => update_binary(f, ab, n, "-", |l, r| l - r),
                BVOperator::Mul => update_binary(f, ab, n, "*", |l, r| l * r),
                BVOperator::Divu => update_binary(f, ab, n, "/", |l, r| l / r),
                BVOperator::BitwiseAnd => update_binary(f, ab, n, "&", |l, r| l & r),
                BVOperator::Sltu => update_binary(f, ab, n, "<", |l, r| {
                    if l < r {
                        BitVector(1)
                    } else {
                        BitVector(0)
                    }
                }),
                BVOperator::Equals => update_binary(f, ab, n, "=", |l, r| {
                    if l == r {
                        BitVector(1)
                    } else {
                        BitVector(0)
                    }
                }),
                BVOperator::Not => update_unary(f, ab, n, "!", |x| {
                    if x == BitVector(0) {
                        BitVector(1)
                    } else {
                        BitVector(0)
                    }
                }),
            }
            f.neighbors_directed(n, Direction::Outgoing)
                .for_each(|n| propagate_assignment(f, ab, n));
        }
        _ => unreachable!(),
    }
}

// can only handle one Equals constrain with constant
fn sat(
    formula: &Formula,
    root: SymbolId,
    mut ab: Assignment<BitVector>,
    timeout_time: Duration,
) -> Result<Option<Assignment<BitVector>>, SolverError> {
    let mut iterations = 0;

    let start_time = Instant::now();

    while ab[root.index()] != BitVector(1) {
        let mut n = root;
        let mut t = BitVector(1);

        iterations += 1;
        trace!("search {}: x{} <- 0x1", iterations, root.index());

        while !is_leaf(formula, n) {
            if start_time.elapsed() > timeout_time {
                return Err(SolverError::Timeout);
            }
            let (v, nx) = match formula[n] {
                Node::Operator(op) => {
                    if op.is_unary() {
                        let nx = get_operand(formula, n);

                        let v = compute_inverse_value_for_unary_op(op, t);

                        trace!(
                            "search {}: x{}({:#x}) = {}x{}({:#x}) |- x{} <- {:#x}",
                            iterations,
                            n.index(),
                            t.0,
                            op,
                            nx.index(),
                            ab[nx.index()].0,
                            nx.index(),
                            v.0
                        );

                        (v, nx)
                    } else {
                        let (nx, ns, side) = select(formula, n, t, &ab);

                        let v = value(formula, n, ns, side, t, &ab);

                        if log_enabled!(Level::Trace) {
                            let (lhs, rhs) = if side == OperandSide::Lhs {
                                (nx, ns)
                            } else {
                                (ns, nx)
                            };

                            trace!(
                                "search {}: x{}({:#x}) := x{}({:#x}) {} x{}({:#x}) |- x{} <- {:#x}",
                                iterations,
                                n.index(),
                                t.0,
                                lhs.index(),
                                ab[lhs.index()].0,
                                op,
                                rhs.index(),
                                ab[rhs.index()].0,
                                nx.index(),
                                v.0
                            );
                        }

                        (v, nx)
                    }
                }
                _ => panic!("non instruction node found"),
            };

            t = v;
            n = nx;
        }

        update_assignment(formula, &mut ab, n, t);
    }

    Ok(Some(ab))
}

#[cfg(test)]
mod tests {
    use super::*;
    //use crate::engine::SyscallId::Openat;

    fn create_formula_with_input() -> (Formula, SymbolId) {
        let mut formula = Formula::new();

        let input = Node::Input(String::from("x0"));
        let input_idx = formula.add_node(input);

        (formula, input_idx)
    }

    fn add_equals_constrain(
        formula: &mut Formula,
        to: SymbolId,
        on: OperandSide,
        constant: u64,
    ) -> SymbolId {
        let constrain = Node::Operator(BVOperator::Equals);
        let constrain_idx = formula.add_node(constrain);

        let constrain_c = Node::Constant(constant);
        let constrain_c_idx = formula.add_node(constrain_c);

        formula.add_edge(to, constrain_idx, on);
        formula.add_edge(constrain_c_idx, constrain_idx, on.other());

        constrain_idx
    }

    #[test]
    fn solve_trivial_equals_constrain() {
        let (mut formula, input_idx) = create_formula_with_input();

        let root = add_equals_constrain(&mut formula, input_idx, OperandSide::Lhs, 10);

        let solver = MonsterSolver::default();
        let result = solver.solve(&formula, root);

        assert!(result.is_ok(), "solver did not time out");
        let unwrapped_result = result.unwrap();

        assert!(
            unwrapped_result.is_some(),
            "has result for trivial equals constrain"
        );
        assert_eq!(
            unwrapped_result.unwrap()[input_idx.index()],
            BitVector(10),
            "solver result of trivial equal constrain has right value"
        );
    }

    #[test]
    fn solve_bvadd() {
        let (mut formula, input_idx) = create_formula_with_input();

        let constant = Node::Constant(3);
        let constant_idx = formula.add_node(constant);

        let instr = Node::Operator(BVOperator::Add);
        let instr_idx = formula.add_node(instr);

        formula.add_edge(input_idx, instr_idx, OperandSide::Lhs);
        formula.add_edge(constant_idx, instr_idx, OperandSide::Rhs);

        let root = add_equals_constrain(&mut formula, instr_idx, OperandSide::Lhs, 10);

        let solver = MonsterSolver::default();
        let result = solver.solve(&formula, root);

        assert!(result.is_ok(), "solver did not time out");
        let unwrapped_result = result.unwrap();

        assert!(unwrapped_result.is_some(), "has result for trivial add op");
        assert_eq!(
            unwrapped_result.unwrap()[input_idx.index()],
            BitVector(7),
            "solver result of trivial add op has right value"
        );
    }

    fn test_invertability(
        op: BVOperator,
        s: u64,
        t: u64,
        d: OperandSide,
        result: bool,
        msg: &'static str,
    ) {
        let s = BitVector(s);
        let t = BitVector(t);

        match d {
            OperandSide::Lhs => {
                assert_eq!(
                    is_invertable(op, s, t, d),
                    result,
                    "x {:?} {:?} == {:?}   {}",
                    op,
                    s,
                    t,
                    msg
                );
            }
            OperandSide::Rhs => {
                assert_eq!(
                    is_invertable(op, s, t, d),
                    result,
                    "{:?} {:?} x == {:?}   {}",
                    s,
                    op,
                    t,
                    msg
                );
            }
        }
    }

    fn test_inverse_value_computation<F>(op: BVOperator, s: u64, t: u64, d: OperandSide, f: F)
    where
        F: FnOnce(BitVector, BitVector) -> BitVector,
    {
        let s = BitVector(s);
        let t = BitVector(t);

        let computed = compute_inverse_value(op, s, t, d);

        // prove: computed <> s == t        where <> is the binary operator

        match d {
            OperandSide::Lhs => {
                assert_eq!(
                    f(computed, s),
                    t,
                    "{:?} {:?} {:?} == {:?}",
                    computed,
                    op,
                    s,
                    t
                );
            }
            OperandSide::Rhs => {
                assert_eq!(
                    f(s, computed),
                    t,
                    "{:?} {:?} {:?} == {:?}",
                    s,
                    op,
                    computed,
                    t
                );
            }
        }
    }

    fn test_consistent_value_computation<F>(op: BVOperator, t: u64, d: OperandSide, f: F)
    where
        F: FnOnce(BitVector, BitVector) -> BitVector,
    {
        let t = BitVector(t);

        let computed = compute_consistent_value(op, t, d);

        // TODO: How to test consistent values?
        // To proof that there exists a y, we would have to compute and inverse value, which is not
        // always possible.
        // I think, Alastairs
        // prove: Ey.(computed <> y == t)        where <> is the binary bit vector operator
        //

        let inverse = match op {
            BVOperator::Add => t - computed,
            BVOperator::Mul => {
                assert!(
                    is_invertable(op, computed, t, d),
                    "choose values which are invertable..."
                );

                compute_inverse_value(op, computed, t, d)
            }
            BVOperator::Sltu => compute_inverse_value(op, computed, t, d),
            BVOperator::Divu => {
                assert!(is_invertable(op, computed, t, d));
                compute_inverse_value(op, computed, t, d)
            }
            _ => unimplemented!(),
        };

        if d == OperandSide::Lhs {
            assert_eq!(
                f(inverse, computed),
                t,
                "{:?} {:?} {:?} == {:?}",
                inverse,
                op,
                computed,
                t
            );
        } else {
            assert_eq!(
                f(computed, inverse),
                t,
                "{:?} {:?} {:?} == {:?}",
                computed,
                op,
                inverse,
                t
            );
        }
    }

    // TODO: add tests for ADD
    // TODO: add tests for SUB

    const MUL: BVOperator = BVOperator::Mul;
    const SLTU: BVOperator = BVOperator::Sltu;
    const DIVU: BVOperator = BVOperator::Divu;

    #[test]
    fn check_invertability_condition_for_divu() {
        test_invertability(DIVU, 0b1, 0b1, OperandSide::Lhs, true, "trivial divu");
        test_invertability(DIVU, 0b1, 0b1, OperandSide::Rhs, true, "trivial divu");

        test_invertability(DIVU, 3, 2, OperandSide::Lhs, true, "x / 3 = 2");
        test_invertability(DIVU, 6, 2, OperandSide::Rhs, true, "6 / x = 2");

        test_invertability(DIVU, 0, 2, OperandSide::Lhs, false, "x / 0 = 2");
        test_invertability(DIVU, 0, 2, OperandSide::Rhs, false, "0 / x = 2");

        test_invertability(DIVU, 5, 6, OperandSide::Rhs, false, "5 / x = 6");
    }

    #[test]
    fn check_invertability_condition_for_mul() {
        let side = OperandSide::Lhs;

        test_invertability(MUL, 0b1, 0b1, side, true, "trivial multiplication");
        test_invertability(MUL, 0b10, 0b1, side, false, "operand bigger than result");
        test_invertability(
            MUL,
            0b10,
            0b10,
            side,
            true,
            "operand with undetermined bits and possible invsere",
        );
        test_invertability(
            MUL,
            0b10,
            0b10,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
        test_invertability(
            MUL,
            0b100,
            0b100,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
        test_invertability(
            MUL,
            0b10,
            0b1100,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
    }

    #[test]
    fn compute_inverse_values_for_divu() {
        fn f(l: BitVector, r: BitVector) -> BitVector {
            l / r
        }

        // test only for values which are actually invertable
        test_inverse_value_computation(DIVU, 0b1, 0b1, OperandSide::Lhs, f);
        test_inverse_value_computation(DIVU, 0b1, 0b1, OperandSide::Rhs, f);

        test_inverse_value_computation(DIVU, 2, 3, OperandSide::Lhs, f);
        test_inverse_value_computation(DIVU, 6, 2, OperandSide::Rhs, f);
    }

    #[test]
    fn check_invertability_condition_for_sltu() {
        let mut side = OperandSide::Lhs;

        test_invertability(SLTU, 0, 1, side, false, "x < 0 == 1 FALSE");
        test_invertability(SLTU, 1, 1, side, true, "x < 1 == 1 TRUE");
        test_invertability(
            SLTU,
            u64::max_value(),
            0,
            side,
            true,
            "x < max_value == 0 TRUE",
        );

        side = OperandSide::Rhs;

        test_invertability(SLTU, 0, 1, side, true, "0 < x == 1 TRUE");
        test_invertability(SLTU, 0, 0, side, true, "0 < x == 0 TRUE");
        test_invertability(
            SLTU,
            u64::max_value(),
            1,
            side,
            false,
            "max_value < x == 1 FALSE",
        );
        test_invertability(
            SLTU,
            u64::max_value(),
            0,
            side,
            true,
            "max_value < x == 0 TRUE",
        );
    }

    #[test]
    fn compute_inverse_values_for_mul() {
        let side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            l * r
        }

        // test only for values which are actually invertable
        test_inverse_value_computation(MUL, 0b1, 0b1, side, f);
        test_inverse_value_computation(MUL, 0b10, 0b10, side, f);
        test_inverse_value_computation(MUL, 0b100, 0b100, side, f);
        test_inverse_value_computation(MUL, 0b10, 0b1100, side, f);
    }

    #[test]
    fn compute_inverse_values_for_sltu() {
        let mut side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            if l < r {
                BitVector(1)
            } else {
                BitVector(0)
            }
        }

        // test only for values which are actually invertable
        test_inverse_value_computation(SLTU, u64::max_value(), 0, side, f);
        test_inverse_value_computation(SLTU, 0, 0, side, f);
        test_inverse_value_computation(SLTU, 1, 1, side, f);

        side = OperandSide::Rhs;

        test_inverse_value_computation(SLTU, 0, 0, side, f);
        test_inverse_value_computation(SLTU, u64::max_value() - 1, 1, side, f);
        test_inverse_value_computation(SLTU, 1, 1, side, f);
    }

    #[test]
    fn compute_consistent_values_for_mul() {
        let side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            l * r
        }

        // test only for values which actually have a consistent value
        test_consistent_value_computation(MUL, 0b110, side, f);
        test_consistent_value_computation(MUL, 0b101, side, f);
        test_consistent_value_computation(MUL, 0b11, side, f);
        test_consistent_value_computation(MUL, 0b100, side, f);
    }

    #[test]
    fn compute_consistent_values_for_sltu() {
        let mut side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            if l < r {
                BitVector(1)
            } else {
                BitVector(0)
            }
        }

        // test only for values which actually have a consistent value
        test_consistent_value_computation(SLTU, 0, side, f);
        test_consistent_value_computation(SLTU, 1, side, f);

        side = OperandSide::Rhs;

        // test only for values which actually have a consistent value
        test_consistent_value_computation(SLTU, 0, side, f);
        test_consistent_value_computation(SLTU, 1, side, f);
    }
}

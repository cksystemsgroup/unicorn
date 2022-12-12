use crate::unicorn::NodeRef;
use std::time::Duration;

//
// Public Interface
//

#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq)]
pub enum Solution {
    Sat,
    Unsat,
    Timeout,
}

// TODO: Clippy in Rust 1.60.0 is overly pedantic. Revisit this on Rust
// upgrades to an even higher version number.
#[allow(clippy::wrong_self_convention)]
pub trait Solver {
    fn new(timeout: Option<Duration>) -> Self;
    fn name() -> &'static str;
    fn solve(&mut self, root: &NodeRef) -> Solution;
    fn is_always_true(&mut self, node: &NodeRef) -> bool;
    fn is_always_false(&mut self, node: &NodeRef) -> bool;
    fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool;
}

//
// Private Implementation
//

// TODO: Move this module into separate file.
pub mod none_impl {
    use crate::unicorn::solver::{Solution, Solver};
    use crate::unicorn::NodeRef;
    use std::time::Duration;

    pub struct NoneSolver {}

    impl Solver for NoneSolver {
        fn name() -> &'static str {
            "None"
        }

        fn new(_timeout: Option<Duration>) -> Self {
            Self {}
        }

        fn is_always_true(&mut self, _node: &NodeRef) -> bool {
            false
        }

        fn is_always_false(&mut self, _node: &NodeRef) -> bool {
            false
        }

        fn is_always_equal(&mut self, _left: &NodeRef, _right: &NodeRef) -> bool {
            false
        }

        fn solve(&mut self, _root: &NodeRef) -> Solution {
            Solution::Timeout
        }
    }
}

// TODO: Move this module into separate file.
#[cfg(feature = "boolector")]
pub mod boolector_impl {
    use crate::unicorn::solver::{Solution, Solver};
    use crate::unicorn::{HashableNodeRef, Node, NodeRef, NodeType};
    use boolector_solver::{
        option::{BtorOption, ModelGen, OutputFileFormat},
        Array, Btor, SolverResult, BV,
    };
    use log::debug;
    use std::collections::HashMap;
    use std::rc::Rc;
    use std::time::Duration;

    type ArrayRef = Array<Rc<Btor>>;
    type BitVectorRef = BV<Rc<Btor>>;

    #[derive(Clone)]
    enum BoolectorValue {
        BitVector(BitVectorRef),
        Array(ArrayRef),
    }

    pub struct BoolectorSolver {
        solver: Rc<Btor>,
        mapping: HashMap<HashableNodeRef, BoolectorValue>,
    }

    impl Solver for BoolectorSolver {
        fn name() -> &'static str {
            "Boolector"
        }

        fn new(timeout: Option<Duration>) -> Self {
            let solver = Rc::new(Btor::new());
            // TODO: Properly configure the below options.
            solver.set_opt(BtorOption::ModelGen(ModelGen::All));
            solver.set_opt(BtorOption::Incremental(true));
            solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));
            solver.set_opt(BtorOption::SolverTimeout(timeout));
            Self {
                solver,
                mapping: HashMap::new(),
            }
        }

        fn is_always_true(&mut self, node: &NodeRef) -> bool {
            let bv = self.visit(node).into_bv().not();
            self.solve_impl(bv) == Solution::Unsat
        }

        fn is_always_false(&mut self, node: &NodeRef) -> bool {
            let bv = self.visit(node).into_bv();
            self.solve_impl(bv) == Solution::Unsat
        }

        fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool {
            let bv_left = self.visit(left).into_bv();
            let bv_right = self.visit(right).into_bv();
            let bv = bv_left._ne(&bv_right);
            self.solve_impl(bv) == Solution::Unsat
        }

        fn solve(&mut self, root: &NodeRef) -> Solution {
            let bv = self.visit(root).into_bv();
            self.solve_impl(bv.slice(0, 0))
        }
    }

    impl BoolectorSolver {
        fn solve_impl(&mut self, bv: BitVectorRef) -> Solution {
            self.solver.push(1);
            bv.assert();
            let solution = match self.solver.sat() {
                SolverResult::Sat => Solution::Sat,
                SolverResult::Unsat => Solution::Unsat,
                SolverResult::Unknown => Solution::Timeout,
            };
            self.solver.pop(1);
            if solution == Solution::Timeout {
                debug!("Query timeout was reached by Boolector");
            }
            solution
        }

        fn visit(&mut self, node: &NodeRef) -> BoolectorValue {
            let key = HashableNodeRef::from(node.clone());
            self.mapping.get(&key).cloned().unwrap_or_else(|| {
                let value = self.translate(node);
                assert!(!self.mapping.contains_key(&key));
                self.mapping.insert(key, value.clone());
                value
            })
        }

        #[rustfmt::skip]
        fn translate(&mut self, node: &NodeRef) -> BoolectorValue {
            match &*node.borrow() {
                Node::Const { sort, imm, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::from_u64(self.solver.clone(), *imm, width).into()
                }
                Node::Read { memory, address, .. } => {
                    let array_memory = self.visit(memory).into_array();
                    let bv_address = self.visit(address).into_bv();
                    array_memory.read(&bv_address).into()
                }
                Node::Write { memory, address, value, .. } => {
                    let array_memory = self.visit(memory).into_array();
                    let bv_address = self.visit(address).into_bv();
                    let bv_value = self.visit(value).into_bv();
                    array_memory.write(&bv_address, &bv_value).into()
                }
                Node::Add { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.add(&bv_right).into()
                }
                Node::Sub { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.sub(&bv_right).into()
                }
                Node::Mul { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.mul(&bv_right).into()
                }
                Node::Div { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.udiv(&bv_right).into()
                },
                Node::Rem { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.urem(&bv_right).into()
                }
                Node::Sll { .. } => todo!("implement SLL"),
                Node::Srl { .. } => todo!("implement SRL"),
                Node::Ult { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.ult(&bv_right).into()
                }
                Node::Ext { from, value, .. } => {
                    let width = from.bitsize() as u32;
                    let bv_value = self.visit(value).into_bv();
                    assert_eq!(bv_value.get_width(), width);
                    bv_value.uext(64 - width).into()
                }
                Node::Ite { sort: NodeType::Memory, cond, left, right, .. } => {
                    let bv_cond = self.visit(cond).into_bv();
                    let array_left = self.visit(left).into_array();
                    let array_right = self.visit(right).into_array();
                    bv_cond.cond_array(&array_left, &array_right).into()
                }
                Node::Ite { sort, cond, left, right, .. } => {
                    let width = sort.bitsize() as u32;
                    let bv_cond = self.visit(cond).into_bv();
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    assert_eq!(bv_left.get_width(), width);
                    assert_eq!(bv_right.get_width(), width);
                    bv_cond.cond_bv(&bv_left, &bv_right).into()
                }
                Node::Eq { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left._eq(&bv_right).into()
                }
                Node::And { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.and(&bv_right).into()
                }
                Node::Not { value, .. } => {
                    let bv_value = self.visit(value).into_bv();
                    bv_value.not().into()
                }
                Node::State { sort: NodeType::Memory, name, .. } => {
                    Array::new(self.solver.clone(), 64, 64, name.as_deref()).into()
                }
                Node::State { sort, name, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::new(self.solver.clone(), width, name.as_deref()).into()
                }
                Node::Input { sort, name, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::new(self.solver.clone(), width, Some(name)).into()
                }
                Node::Next { .. } => panic!("should be unreachable"),
                Node::Bad { .. } => panic!("should be unreachable"),
                Node::Comment(_) => panic!("cannot translate"),
            }
        }
    }

    impl From<BitVectorRef> for BoolectorValue {
        fn from(item: BitVectorRef) -> Self {
            Self::BitVector(item)
        }
    }

    impl From<ArrayRef> for BoolectorValue {
        fn from(item: ArrayRef) -> Self {
            Self::Array(item)
        }
    }

    impl BoolectorValue {
        fn into_bv(self) -> BitVectorRef {
            match self {
                BoolectorValue::BitVector(x) => x,
                _ => panic!("expected bit-vector"),
            }
        }
        fn into_array(self) -> ArrayRef {
            match self {
                BoolectorValue::Array(x) => x,
                _ => panic!("expected array"),
            }
        }
    }
}

// TODO: Move this module into separate file.
#[cfg(feature = "z3")]
pub mod z3solver_impl {
    use crate::unicorn::solver::{Solution, Solver};
    use crate::unicorn::{HashableNodeRef, Node, NodeRef, NodeType};
    use log::debug;
    use std::collections::HashMap;
    use std::convert::TryInto;
    use std::time::Duration;
    use z3_solver::{
        ast::{Array, Ast, Bool, Dynamic, BV},
        Config, Context, SatResult, Solver as Z3Solver, Sort,
    };

    pub struct Z3SolverWrapper<'ctx> {
        context: &'ctx Context,
        solver: Z3Solver<'ctx>,
        mapping: HashMap<HashableNodeRef, Dynamic<'ctx>>,
        zero: BV<'ctx>,
        one: BV<'ctx>,
    }

    impl<'ctx> Solver for Z3SolverWrapper<'ctx> {
        fn name() -> &'static str {
            "Z3"
        }

        fn new(timeout: Option<Duration>) -> Self {
            let mut config = Config::new();
            if let Some(duration) = timeout {
                config.set_timeout_msec(duration.as_millis().try_into().expect("fits in u64"));
            }
            let context = Context::new(&config);
            // TODO: This is very funky, avoid leaking context.
            let leak: &'ctx Context = Box::leak(Box::new(context));
            Self {
                context: leak,
                solver: Z3Solver::new(leak),
                mapping: HashMap::new(),
                zero: BV::from_u64(leak, 0, 64),
                one: BV::from_u64(leak, 1, 64),
            }
        }

        fn is_always_true(&mut self, node: &NodeRef) -> bool {
            let z3_bool = self.visit(node).as_bool().expect("bool").not();
            self.solve_impl(&z3_bool) == Solution::Unsat
        }

        fn is_always_false(&mut self, node: &NodeRef) -> bool {
            let z3_bool = self.visit(node).as_bool().expect("bool");
            self.solve_impl(&z3_bool) == Solution::Unsat
        }

        fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool {
            let z3_left = Dynamic::from_ast(self.visit(left));
            let z3_right = Dynamic::from_ast(self.visit(right));
            let z3_bool = z3_left._eq(&z3_right).not();
            self.solve_impl(&z3_bool) == Solution::Unsat
        }

        fn solve(&mut self, root: &NodeRef) -> Solution {
            let z3_bool = self.visit(root).as_bool().expect("bool");
            self.solve_impl(&z3_bool)
        }
    }

    impl<'ctx> Z3SolverWrapper<'ctx> {
        fn solve_impl(&mut self, z3_bool: &Bool<'ctx>) -> Solution {
            self.solver.push();
            self.solver.assert(z3_bool);
            let solution = match self.solver.check() {
                SatResult::Sat => Solution::Sat,
                SatResult::Unsat => Solution::Unsat,
                SatResult::Unknown => Solution::Timeout,
            };
            self.solver.pop(1);
            if solution == Solution::Timeout {
                debug!("Query timeout was reached by Z3");
            }
            solution
        }

        fn visit(&mut self, node: &NodeRef) -> &Dynamic<'ctx> {
            let key = HashableNodeRef::from(node.clone());
            if !self.mapping.contains_key(&key) {
                let value = self.translate(node);
                assert!(!self.mapping.contains_key(&key));
                self.mapping.insert(key.clone(), value);
            }
            &self.mapping[&key]
        }

        #[rustfmt::skip]
        fn translate(&mut self, node: &NodeRef) -> Dynamic<'ctx> {
            match &*node.borrow() {
                Node::Const { sort: NodeType::Bit, imm, .. } => {
                    Bool::from_bool(self.context, *imm != 0).into()
                }
                Node::Const { sort, imm, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::from_u64(self.context, *imm, width).into()
                }
                Node::Read { memory, address, .. } => {
                    let z3_memory = self.visit(memory).as_array().expect("array");
                    let z3_address = self.visit(address).as_bv().expect("bv");
                    z3_memory.select(&z3_address)
                }
                Node::Write { memory, address, value, .. } => {
                    let z3_memory = self.visit(memory).as_array().expect("array");
                    let z3_address = self.visit(address).as_bv().expect("bv");
                    let z3_value = self.visit(value).as_bv().expect("bv");
                    z3_memory.store(&z3_address, &z3_value).into()
                }
                Node::Add { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvadd(&z3_right).into()
                }
                Node::Sub { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvsub(&z3_right).into()
                }
                Node::Mul { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvmul(&z3_right).into()
                }
                Node::Div { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvudiv(&z3_right).into()
                }
                Node::Rem { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvurem(&z3_right).into()
                }
                Node::Sll { .. } => todo!("implement SLL"),
                Node::Srl { .. } => todo!("implement SRL"),
                Node::Ult { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvult(&z3_right).into()
                }
                Node::Ext { from: NodeType::Bit, value, .. } => {
                    let z3_value = self.visit(value).as_bool().expect("bool");
                    z3_value.ite(&self.zero, &self.one).into()
                }
                Node::Ext { from, value, .. } => {
                    let width = from.bitsize() as u32;
                    let z3_value = self.visit(value).as_bv().expect("bv");
                    z3_value.zero_ext(64 - width).into()
                }
                Node::Ite { cond, left, right, .. } => {
                    let z3_cond = self.visit(cond).as_bool().expect("bool");
                    let z3_left = Dynamic::from_ast(self.visit(left));
                    let z3_right = Dynamic::from_ast(self.visit(right));
                    z3_cond.ite(&z3_left, &z3_right)
                }
                Node::Eq { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left._eq(&z3_right).into()
                }
                Node::And { sort: NodeType::Bit, left, right, .. } => {
                    let z3_left = self.visit(left).as_bool().expect("bool");
                    let z3_right = self.visit(right).as_bool().expect("bool");
                    Bool::and(self.context, &[&z3_left, &z3_right]).into()
                }
                Node::And { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvand(&z3_right).into()
                }
                Node::Not { value, .. } => {
                    let z3_value = self.visit(value).as_bool().expect("bool");
                    z3_value.not().into()
                }
                Node::State { sort: NodeType::Bit, name, .. } => {
                    let name = name.as_deref().expect("name");
                    Bool::new_const(self.context, name).into()
                }
                Node::State { sort: NodeType::Memory, name, .. } => {
                    let name = name.as_deref().expect("name");
                    let bv64 = Sort::bitvector(self.context, 64);
                    Array::new_const(self.context, name, &bv64, &bv64).into()
                }
                Node::State { sort, name, .. } => {
                    let width = sort.bitsize() as u32;
                    let name = name.as_deref().expect("name");
                    BV::new_const(self.context, name, width).into()
                }
                Node::Input { sort, name, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::new_const(self.context, name.to_owned(), width).into()
                }
                Node::Next { .. } => panic!("should be unreachable"),
                Node::Bad { .. } => panic!("should be unreachable"),
                Node::Comment(_) => panic!("cannot translate"),
            }
        }
    }
}

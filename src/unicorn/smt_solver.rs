use crate::unicorn::NodeRef;
use std::time::Duration;

//
// Public Interface
//

#[allow(dead_code)]
#[derive(Debug, Eq, PartialEq)]
pub enum SMTSolution {
    Sat,
    Unsat,
    Timeout,
}

pub trait SMTSolver {
    fn new(timeout: Option<Duration>) -> Self;
    fn name() -> &'static str;
    fn solve(&mut self, root: &NodeRef) -> SMTSolution;
    fn solve_n(&mut self, nodes: &Vec<NodeRef>) -> SMTSolution;
    fn is_always_true(&mut self, node: &NodeRef) -> bool;
    fn is_always_false(&mut self, node: &NodeRef) -> bool;
    fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool;
}

//
// Private Implementation
//

// TODO: Move this module into separate file.
pub mod none_impl {
    use crate::unicorn::smt_solver::{SMTSolution, SMTSolver};
    use crate::unicorn::NodeRef;
    use std::time::Duration;

    pub struct NoneSolver {}

    impl SMTSolver for NoneSolver {
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

        fn solve(&mut self, _root: &NodeRef) -> SMTSolution {
            SMTSolution::Timeout
        }

        fn solve_n(&mut self, _nodes: &Vec<NodeRef>) -> SMTSolution {
          SMTSolution::Timeout
        }
    }
}

// TODO: Move this module into separate file.
#[cfg(feature = "boolector")]
pub mod boolector_impl {
    use crate::unicorn::smt_solver::{SMTSolution, SMTSolver};
    use crate::unicorn::{HashableNodeRef, Node, NodeRef, NodeType};
    use boolector_solver::{
        option::{BtorOption, ModelGen, OutputFileFormat},
        Array, Btor, SolverResult, BV,
    };
    use log::debug;
    use std::collections::HashMap;
    use std::rc::Rc;
    use std::time::Duration;
    use boolector_solver::option::SolverEngine;

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

    impl SMTSolver for BoolectorSolver {
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
            solver.set_opt(BtorOption::EliminateSlices(true));
            solver.set_opt(BtorOption::VariableSubst(true));
            solver.set_opt(BtorOption::FunPreProp(true));
            solver.set_opt(BtorOption::FunPreSLS(true));
            solver.set_opt(BtorOption::FunJustification(true));
            Self {
                solver,
                mapping: HashMap::new(),
            }
        }

        fn is_always_true(&mut self, node: &NodeRef) -> bool {
            let bv = self.visit(node).into_bv().not();
            self.solve_impl(bv) == SMTSolution::Unsat
        }

        fn is_always_false(&mut self, node: &NodeRef) -> bool {
            let bv = self.visit(node).into_bv();
            self.solve_impl(bv) == SMTSolution::Unsat
        }

        fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool {
            let bv_left = self.visit(left).into_bv();
            let bv_right = self.visit(right).into_bv();
            let bv = bv_left._ne(&bv_right);
            self.solve_impl(bv) == SMTSolution::Unsat
        }

        fn solve(&mut self, root: &NodeRef) -> SMTSolution {
            let bv = self.visit(root).into_bv();
            self.solve_impl(bv.slice(0, 0))
        }

        fn solve_n(&mut self, nodes: &Vec<NodeRef>) -> SMTSolution {
          let bv = BV::zero(self.solver.clone(), 1);
          for node in nodes.iter() {
            bv.or(&self.visit(node).into_bv());
          }
          self.solve_impl(bv)
        }
    }

    impl BoolectorSolver {
        fn solve_impl(&mut self, bv: BitVectorRef) -> SMTSolution {
            self.solver.push(1);
            bv.assert();
            let solution = match self.solver.sat() {
                SolverResult::Sat => SMTSolution::Sat,
                SolverResult::Unsat => SMTSolution::Unsat,
                SolverResult::Unknown => SMTSolution::Timeout,
            };
            self.solver.pop(1);
            if solution == SMTSolution::Timeout {
                debug!("Query timeout was reached by Boolector");
            }
            solution
        }

        fn visit(&mut self, node: &NodeRef) -> BoolectorValue {
            let key = HashableNodeRef::from(node.clone());
            /*match &*node.borrow() {
                Node::Input { .. } => println!("input!"),
                _ => {}
            }*/
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
                    /*if *sort == NodeType::Input1Byte {
                        println!("const: input 1 byte!");
                    }*/
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
                    bv_left.sdiv(&bv_right).into()
                },
                Node::Rem { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.urem(&bv_right).into()
                }
                Node::Ult { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.ult(&bv_right).into()
                }
                Node::Ext { from, value, .. } => {
                    let width = from.bitsize() as u32;
                    /*if *from == NodeType::Input1Byte {
                        println!("ext: input 1 byte!");
                        match &*value.borrow() {
                            Node::Const { .. } => println!("ext: const!"),
                            Node::Read { .. } => println!("ext: read!"),
                            Node::Write { .. } => println!("ext: write!"),
                            Node::Add { .. } => println!("ext: add!"),
                            Node::Sub { .. } => println!("ext: sub!"),
                            Node::Mul { .. } => println!("ext: mul!"),
                            Node::Divu { .. } => println!("ext: divu!"),
                            Node::Div { .. } => println!("ext: div!"),
                            Node::Rem { .. } => println!("ext: rem!"),
                            Node::Sll { .. } => println!("ext: sll!"),
                            Node::Srl { .. } => println!("ext: srl!"),
                            Node::Ult { .. } => println!("ext: ult!"),
                            Node::Ext { .. } => println!("ext: ext!"),
                            Node::Ite { sort: NodeType::Memory, .. } => println!("ext: memory ite!"),
                            Node::Ite { .. } => println!("ext: ite!"),
                            Node::Eq { .. } => println!("ext: eq!"),
                            Node::And { .. } => println!("ext: and!"),
                            Node::Or { .. } => println!("ext: or!"),
                            Node::Not { .. } => println!("ext: not!"),
                            Node::State { sort: NodeType::Memory, .. } => println!("ext: memory state!"),
                            Node::State { .. } => println!("ext: state!"),
                            Node::Input { .. } => println!("ext: input!"),
                            Node::Next { .. } => panic!("ext: next should be unreachable!"),
                            Node::Bad { .. } => println!("ext: bad!"),
                            Node::Good { .. } => println!("ext: good!"),
                            Node::Comment { .. } => panic!("ext: comment should be unreachable!"),
                        }
                    }
                    match &*value.borrow() {
                        Node::Input { .. } => println!("input!"),
                        _ => {}
                    }*/
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
                    /*if *sort == NodeType::Input1Byte {
                        println!("ite: input 1 byte!");
                    }*/
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
                Node::Or { left, right, .. } => {
                    let bv_left = self.visit(left).into_bv();
                    let bv_right = self.visit(right).into_bv();
                    bv_left.or(&bv_right).into()
                }
                Node::Not { value, .. } => {
                    let bv_value = self.visit(value).into_bv();
                    bv_value.not().into()
                }
                Node::State { sort: NodeType::Memory, name, init, .. } => {
                    match init {
                        Some(value) => {
                            let array_value = self.visit(value).into_array();
                            array_value.into()
                        }
                        None => Array::new_initialized(self.solver.clone(), 64, 64,
                                                        &BV::from_u64(self.solver.clone(), 0, 64)).into()
                        //Array::new(self.solver.clone(), 64, 64, name.as_deref()).into()
                    }}
                Node::State { sort, name, init, .. } => {
                    let width = sort.bitsize() as u32;
                    /*if *sort == NodeType::Input1Byte {
                        println!("state: input 1 byte!");
                    }*/
                    match init {
                        Some(value) => {
                            /*if *sort == NodeType::Input1Byte {
                                match &*value.borrow() {
                                    Node::Const { .. } => println!("state: const!"),
                                    Node::Read { .. } => println!("state: read!"),
                                    Node::Write { .. } => println!("state: write!"),
                                    Node::Add { .. } => println!("state: add!"),
                                    Node::Sub { .. } => println!("state: sub!"),
                                    Node::Mul { .. } => println!("state: mul!"),
                                    Node::Divu { .. } => println!("state: divu!"),
                                    Node::Div { .. } => println!("state: div!"),
                                    Node::Rem { .. } => println!("state: rem!"),
                                    Node::Sll { .. } => println!("state: sll!"),
                                    Node::Srl { .. } => println!("state: srl!"),
                                    Node::Ult { .. } => println!("state: ult!"),
                                    Node::Ext { .. } => println!("state: ext!"),
                                    Node::Ite { sort: NodeType::Memory, .. } => println!("state: memory ite!"),
                                    Node::Ite { .. } => println!("state: ite!"),
                                    Node::Eq { .. } => println!("state: eq!"),
                                    Node::And { .. } => println!("state: and!"),
                                    Node::Or { .. } => println!("state: or!"),
                                    Node::Not { .. } => println!("state: not!"),
                                    Node::State { sort: NodeType::Memory, .. } => println!("state: memory state!"),
                                    Node::State { .. } => println!("state: state!"),
                                    Node::Input { .. } => println!("state: input!"),
                                    Node::Next { .. } => panic!("state: next should be unreachable!"),
                                    Node::Bad { .. } => println!("state: bad!"),
                                    Node::Good { .. } => println!("state: good!"),
                                    Node::Comment { .. } => panic!("state: comment should be unreachable!"),
                                }
                            }*/
                            let bv_value = self.visit(value).into_bv();
                            assert_eq!(bv_value.get_width(), width);
                            bv_value.into()
                        }
                        None => BV::new(self.solver.clone(), width, name.as_deref()).into()
                    }
                }
                Node::Input { sort, name, .. } => {
                    let width = sort.bitsize() as u32;
                    /*if *sort == NodeType::Input1Byte {
                        println!("input: input 1 byte!");
                    }
                    println!("input is reached!");*/
                    BV::new(self.solver.clone(), width, Some(name)).into()
                }
                Node::Next { .. } => panic!("should be unreachable"),
                Node::Bad { cond, .. } => {
                    self.visit(cond)
                },
                Node::Good { cond, .. } => {
                    self.visit(cond)
                },
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
    use crate::unicorn::smt_solver::{SMTSolution, SMTSolver};
    use crate::unicorn::{HashableNodeRef, Node, NodeRef, NodeType};
    use log::debug;
    use std::collections::HashMap;
    use std::convert::TryInto;
    use std::time::Duration;
    use z3_solver::{ast::{Array, Ast, Bool, Dynamic, BV}, Config, Context, SatResult, Solver as Z3Solver, Sort};

    pub struct Z3SolverWrapper<'ctx> {
        context: &'ctx Context,
        solver: Z3Solver<'ctx>,
        mapping: HashMap<HashableNodeRef, Dynamic<'ctx>>,
        zero: BV<'ctx>,
        one: BV<'ctx>,
    }

    impl<'ctx> SMTSolver for Z3SolverWrapper<'ctx> {
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
            self.solve_impl(&z3_bool) == SMTSolution::Unsat
        }

        fn is_always_false(&mut self, node: &NodeRef) -> bool {
            let z3_bool = self.visit(node).as_bool().expect("bool");
            self.solve_impl(&z3_bool) == SMTSolution::Unsat
        }

        fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool {
            let z3_left = Dynamic::from_ast(self.visit(left));
            let z3_right = Dynamic::from_ast(self.visit(right));
            let z3_bool = z3_left._eq(&z3_right).not();
            self.solve_impl(&z3_bool) == SMTSolution::Unsat
        }

        fn solve(&mut self, root: &NodeRef) -> SMTSolution {
            let z3_bool = self.visit(root).as_bool().expect("bool");
            self.solve_impl(&z3_bool)
        }

        fn solve_n(&mut self, _nodes: &Vec<NodeRef>) -> SMTSolution {
          SMTSolution::Timeout
        }
    }

    impl<'ctx> Z3SolverWrapper<'ctx> {
        fn solve_impl(&mut self, z3_bool: &Bool<'ctx>) -> SMTSolution {
            self.solver.push();
            self.solver.assert(&z3_bool.simplify());
            let solution = match self.solver.check() {
                SatResult::Sat => SMTSolution::Sat,
                SatResult::Unsat => SMTSolution::Unsat,
                SatResult::Unknown => SMTSolution::Timeout,
            };
            self.solver.pop(1);
            if solution == SMTSolution::Timeout {
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
                    z3_memory.select(&z3_address).simplify()
                }
                Node::Write { memory, address, value, .. } => {
                    let z3_memory = self.visit(memory).as_array().expect("array");
                    let z3_address = self.visit(address).as_bv().expect("bv");
                    let z3_value = self.visit(value).as_bv().expect("bv");
                    z3_memory.store(&z3_address, &z3_value).simplify().into()
                }
                Node::Add { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvadd(&z3_right).simplify().into()
                }
                Node::Sub { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvsub(&z3_right).simplify().into()
                }
                Node::Mul { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvmul(&z3_right).simplify().into()
                }
                Node::Div { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvsdiv(&z3_right).simplify().into()
                }
                Node::Rem { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvurem(&z3_right).simplify().into()
                }
                Node::Ult { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvult(&z3_right).into()
                }
                Node::Ext { from: NodeType::Bit, value, .. } => {
                    let z3_value = self.visit(value).as_bool().expect("bool");
                    z3_value.ite(&self.zero, &self.one).simplify().into()
                }
                Node::Ext { from, value, .. } => {
                    let width = from.bitsize() as u32;
                    let z3_value = self.visit(value).as_bv().expect("bv");
                    z3_value.zero_ext(64 - width).simplify().into()
                }
                Node::Ite { cond, left, right, .. } => {
                    let z3_cond = self.visit(cond).as_bool().expect("bool");
                    let z3_left = Dynamic::from_ast(self.visit(left));
                    let z3_right = Dynamic::from_ast(self.visit(right));
                    z3_cond.ite(&z3_left, &z3_right).simplify()
                }
                Node::Eq { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left._eq(&z3_right).simplify().into()
                }
                Node::And { sort: NodeType::Bit, left, right, .. } => {
                    let z3_left = self.visit(left).as_bool().expect("bool");
                    let z3_right = self.visit(right).as_bool().expect("bool");
                    Bool::and(self.context, &[&z3_left, &z3_right]).simplify().into()
                }
                Node::And { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvand(&z3_right).simplify().into()
                }
                Node::Or { sort: NodeType::Bit, left, right, .. } => {
                    let z3_left = self.visit(left).as_bool().expect("bool");
                    let z3_right = self.visit(right).as_bool().expect("bool");
                    Bool::or(self.context, &[&z3_left, &z3_right]).simplify().into()
                }
                Node::Or { left, right, .. } => {
                    let z3_left = self.visit(left).as_bv().expect("bv");
                    let z3_right = self.visit(right).as_bv().expect("bv");
                    z3_left.bvor(&z3_right).simplify().into()
                }
                Node::Not { sort: NodeType::Bit, value, .. } => {
                    let z3_value = self.visit(value).as_bool().expect("bool");
                    z3_value.not().simplify().into()
                }
                Node::Not { value, .. } => {
                    let z3_value = self.visit(value).as_bv().expect("bv");
                    z3_value.bvnot().simplify().into()
                }
                Node::State { sort: NodeType::Bit, name, init, .. } => {
                    let name = name.as_deref().expect("name");
                    match init {
                        Some(value) => {
                            let z3_value = self.visit(value).as_bool().expect("bool");
                            z3_value.simplify().into()
                        }
                        None => Bool::new_const(self.context, name).into()
                    }
                }
                Node::State { sort: NodeType::Memory, name, init, .. } => {
                    //let name = name.as_deref().expect("name");
                    let bv64 = Sort::bitvector(self.context, 64);
                    //Array:::new_const(self.context, name, &bv64, &bv64).into()
                    match init {
                        Some(value) => {
                            let z3_value = self.visit(value).as_array().expect("array");
                            z3_value.simplify().into()
                        }
                        None => Array::const_array(self.context, &bv64,
                                                   &BV::from_u64(self.context, 0, 64)).into()
                    }
                }
                Node::State { sort, name, init, .. } => {
                    let width = sort.bitsize() as u32;
                    let name = name.as_deref().expect("name");
                    match init {
                        Some(value) => {
                            let z3_value = self.visit(value).as_bv().expect("bv");
                            z3_value.simplify().into()
                        }
                        None => BV::new_const(self.context, name, width).into()
                    }
                }
                Node::Input { sort, name, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::new_const(self.context, name.to_owned(), width).into()
                }
                Node::Next { .. } => panic!("should be unreachable"),
                Node::Bad { cond, .. } => {
                    // TODO: It would be better if we would directly referece the condition instead of referencing the Bad node in the OR'ed graph. That way Bad conceptually remains as not producing any output and the graph that smt_solver.rs sees is still purely combinatorial. 
                    self.visit(cond).simplify().clone()
                },
                Node::Good { cond, .. } => {
                    // TODO: It would be better if we would directly referece the condition instead of referencing the Good node in the OR'ed graph. That way Good conceptually remains as not producing any output and the graph that smt_solver.rs sees is still purely combinatorial.
                    self.visit(cond).simplify().clone()
                },
                Node::Comment(_) => panic!("cannot translate"),
            }
        }
    }
}

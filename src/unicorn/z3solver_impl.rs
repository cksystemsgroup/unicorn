
#[cfg(feature = "z3")]
use crate::unicorn::solver::{Solution, Solver};
#[cfg(feature = "z3")]
use crate::unicorn::{HashableNodeRef, Node, NodeRef, NodeType};
#[cfg(feature = "z3")]
use std::collections::HashMap;

#[cfg(feature = "z3")]
use z3_solver::{
    ast::{Ast, Bool, Dynamic, BV},
    Config, Context, SatResult, Solver as Z3Solver,
};

#[cfg(feature = "z3")]
pub struct Z3SolverWrapper<'ctx> {
    context: &'ctx Context,
    solver: Z3Solver<'ctx>,
    mapping: HashMap<HashableNodeRef, Dynamic<'ctx>>,
    zero: BV<'ctx>,
    one: BV<'ctx>,
}

#[cfg(feature = "z3")]
impl<'ctx> Solver for Z3SolverWrapper<'ctx> {
    fn name() -> &'static str {
        "Z3"
    }

    fn new() -> Self {
        let config = Config::new();
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

#[cfg(feature = "z3")]
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
            Node::Read { .. } => panic!("missing array logic"),
            Node::Write { .. } => panic!("missing array logic"),
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
            Node::Div { .. } => panic!("implement DIV"),
            Node::Rem { left, right, .. } => {
                let z3_left = self.visit(left).as_bv().expect("bv");
                let z3_right = self.visit(right).as_bv().expect("bv");
                z3_left.bvurem(&z3_right).into()
            }
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
            Node::And { left, right, .. } => {
                let z3_left = self.visit(left).as_bool().expect("bool");
                let z3_right = self.visit(right).as_bool().expect("bool");
                Bool::and(self.context, &[&z3_left, &z3_right]).into()
            }
            Node::Not { value, .. } => {
                let z3_value = self.visit(value).as_bool().expect("bool");
                z3_value.not().into()
            }
            Node::State { sort: NodeType::Bit, name, .. } => {
                let name = name.as_deref().expect("name");
                Bool::new_const(self.context, name).into()
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

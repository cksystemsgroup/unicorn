use crate::{
    bitvec::BitVector,
    solver::{Assignment, Solver, SolverError},
    symbolic_state::{
        get_operands, BVOperator, Formula,
        Node::{Constant, Input, Operator},
        SymbolId,
    },
};
use std::collections::HashMap;
use z3::{
    ast::{Ast, Bool, Dynamic, BV},
    Config, Context, Model, SatResult, Solver as Z3Solver,
};

pub struct Z3 {}

impl Z3 {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for Z3 {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver for Z3 {
    fn name() -> &'static str {
        "Z3"
    }

    fn solve_impl(
        &self,
        graph: &Formula,
        root: SymbolId,
    ) -> Result<Option<Assignment<BitVector>>, SolverError> {
        let config = Config::default();
        let ctx = Context::new(&config);

        let mut translator = Z3Translator::new(graph, &ctx);

        let (root_node, translation) = translator.translate(root);

        let solver = Z3Solver::new(&ctx);

        solver.assert(&root_node);

        match solver.check() {
            SatResult::Sat => {
                let model = solver
                    .get_model()
                    .expect("has an result after calling check()");

                Ok(Some(
                    graph
                        .node_indices()
                        .map(|i| bv_for_node_idx(i, translation, &model))
                        .collect(),
                ))
            }
            SatResult::Unsat => Ok(None),
            SatResult::Unknown => Err(SolverError::SatUnknown),
        }
    }
}

fn bv_for_node_idx<'ctx>(
    i: SymbolId,
    translation: &HashMap<SymbolId, Dynamic<'ctx>>,
    m: &Model,
) -> BitVector {
    let ast_node = translation
        .get(&i)
        .expect("input BV must be always assigned something once solved");

    if let Some(bv) = ast_node.as_bv() {
        let concrete_bv = m
            .eval(&bv)
            .expect("will always get a result because the formula is SAT");

        let result_value = concrete_bv.as_u64().expect("type already checked here");

        BitVector(result_value)
    } else if let Some(b) = ast_node.as_bool() {
        let concrete_bool = m
            .eval(&b)
            .expect("will always get a result because the formula is SAT");

        let result_value = concrete_bool.as_bool().expect("type already checked here");

        if result_value {
            BitVector(1)
        } else {
            BitVector(0)
        }
    } else {
        panic!("only inputs of type BV and Bool are allowed");
    }
}

macro_rules! traverse_binary {
    ($self:expr, $lhs:expr, $op:ident, $rhs:expr) => {{
        let lhs = $self.traverse($lhs);
        let rhs = $self.traverse($rhs);

        Dynamic::from(
            lhs.as_bv()
                .expect("An AST node of type BitVector should be at LHS of this operator")
                .$op(
                    &rhs.as_bv()
                        .expect("An AST node of type BitVector should be at RHS of this operator"),
                ),
        )
    }};
}

struct Z3Translator<'a, 'ctx> {
    graph: &'a Formula,
    ctx: &'ctx Context,
    bvs: HashMap<SymbolId, Dynamic<'ctx>>,
    zero: Dynamic<'ctx>,
    one: Dynamic<'ctx>,
}

impl<'a, 'ctx> Z3Translator<'a, 'ctx> {
    pub fn new(graph: &'a Formula, into: &'ctx Context) -> Self {
        Self {
            graph,
            ctx: into,
            bvs: HashMap::new(),
            zero: Dynamic::from(BV::from_u64(into, 0, 64)),
            one: Dynamic::from(BV::from_u64(into, 1, 64)),
        }
    }

    pub fn translate(&mut self, root: SymbolId) -> (Bool<'ctx>, &HashMap<SymbolId, Dynamic<'ctx>>) {
        self.bvs = HashMap::new();

        let root_node = self.traverse(root);

        (root_node._eq(&self.one), &self.bvs)
    }

    fn traverse(&mut self, node: SymbolId) -> Dynamic<'ctx> {
        let ast_node = match &self.graph[node] {
            Operator(op) => match get_operands(self.graph, node) {
                (lhs, Some(rhs)) => match op {
                    BVOperator::Add => traverse_binary!(self, lhs, bvadd, rhs),
                    BVOperator::Sub => traverse_binary!(self, lhs, bvsub, rhs),
                    BVOperator::Mul => traverse_binary!(self, lhs, bvmul, rhs),
                    BVOperator::Divu => traverse_binary!(self, lhs, bvudiv, rhs),
                    BVOperator::Equals => traverse_binary!(self, lhs, _eq, rhs)
                        .as_bool()
                        .unwrap()
                        .ite(&self.one, &self.zero),
                    BVOperator::BitwiseAnd => {
                        traverse_binary!(self, lhs, bvand, rhs)
                    }
                    BVOperator::Sltu => traverse_binary!(self, lhs, bvult, rhs)
                        .as_bool()
                        .expect("has to be bool after bvslt")
                        .ite(&self.one, &self.zero),
                    i => unreachable!("binary operator: {:?}", i),
                },
                (lhs, None) => match op {
                    BVOperator::Not => self
                        .traverse(lhs)
                        ._eq(&self.zero)
                        .ite(&self.one, &self.zero),
                    i => unreachable!("unary operator: {:?}", i),
                },
            },
            Input(name) => {
                if let Some(value) = self.bvs.get(&node) {
                    value.clone()
                } else {
                    Dynamic::from(BV::new_const(self.ctx, name.clone(), 64))
                }
            }
            Constant(cst) => Dynamic::from(BV::from_u64(self.ctx, *cst, 64)),
        };

        self.bvs.insert(node, ast_node.clone());

        ast_node
    }
}

use crate::bitvec::BitVector;
use crate::solver::{Assignment, Solver};
use crate::symbolic_state::{
    get_operands, BVOperator, Formula,
    Node::{Constant, Input, Operator},
    SymbolId,
};
use std::collections::HashMap;
use z3::{
    ast::{Ast, Dynamic, BV},
    Config, Context, SatResult, Solver as Z3Solver,
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

    fn solve_impl(&mut self, graph: &Formula, root: SymbolId) -> Option<Assignment<BitVector>> {
        let config = Config::default();
        let ctx = Context::new(&config);

        let mut bvs = HashMap::new();
        let bv = traverse(graph, root, &ctx, &mut bvs);

        let solver = Z3Solver::new(&ctx);

        solver.assert(&bv.as_bool().unwrap());

        match solver.check() {
            SatResult::Sat => {
                let m = solver.get_model().unwrap();

                Some(
                    graph
                        .node_indices()
                        .filter(|i| matches!(graph[*i], Input(_)))
                        .map(|i| {
                            let input_bv = bvs.get(&i).unwrap().as_bv().unwrap();
                            let result_bv = m.eval(&input_bv).unwrap();
                            let result_value = result_bv.as_u64().unwrap();

                            BitVector(result_value)
                        })
                        .collect(),
                )
            }
            _ => None,
        }
    }
}

macro_rules! traverse_binary {
    ($lhs:expr, $op:ident, $rhs:expr, $graph:expr, $ctx:expr, $bvs:expr) => {
        Dynamic::from(
            traverse($graph, $lhs, $ctx, $bvs)
                .as_bv()
                .expect("An AST node of type BitVector should be at this position")
                .$op(
                    &traverse($graph, $rhs, $ctx, $bvs)
                        .as_bv()
                        .expect("An AST node of type BitVector should be at this position"),
                ),
        )
    };
}

fn traverse<'ctx>(
    graph: &Formula,
    node: SymbolId,
    ctx: &'ctx Context,
    bvs: &mut HashMap<SymbolId, Dynamic<'ctx>>,
) -> Dynamic<'ctx> {
    let bv = match &graph[node] {
        Operator(op) => match get_operands(graph, node) {
            (lhs, Some(rhs)) => match op {
                BVOperator::Add => traverse_binary!(lhs, bvadd, rhs, graph, ctx, bvs),
                BVOperator::Sub => traverse_binary!(lhs, bvsub, rhs, graph, ctx, bvs),
                BVOperator::Mul => traverse_binary!(lhs, bvmul, rhs, graph, ctx, bvs),
                BVOperator::Divu => traverse_binary!(lhs, bvudiv, rhs, graph, ctx, bvs),
                BVOperator::Equals => traverse_binary!(lhs, _eq, rhs, graph, ctx, bvs),
                BVOperator::BitwiseAnd => traverse_binary!(lhs, bvand, rhs, graph, ctx, bvs),
                BVOperator::Sltu => traverse_binary!(lhs, bvslt, rhs, graph, ctx, bvs),
                i => unimplemented!("binary operator: {:?}", i),
            },
            (lhs, None) => match op {
                BVOperator::Not => {
                    let zero = BV::from_u64(ctx, 0, 64);
                    Dynamic::from(traverse(graph, lhs, ctx, bvs)._eq(&Dynamic::from(zero)))
                }
                i => unimplemented!("unary operator: {:?}", i),
            },
        },
        Input(name) => {
            if let Some(value) = bvs.get(&node) {
                value.clone()
            } else {
                Dynamic::from(BV::new_const(ctx, name.clone(), 64))
            }
        }
        Constant(cst) => Dynamic::from(BV::from_u64(ctx, *cst, 64)),
    };

    bvs.insert(node, bv.clone());
    bv
}

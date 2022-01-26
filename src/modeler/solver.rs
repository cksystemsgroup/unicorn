use crate::modeler::NodeRef;

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

pub trait Solver {
    fn new() -> Self;
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
    use crate::modeler::solver::{Solution, Solver};
    use crate::modeler::NodeRef;

    pub struct NoneSolver {}

    impl Solver for NoneSolver {
        fn name() -> &'static str {
            "None"
        }

        fn new() -> Self {
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
    use crate::modeler::solver::{Solution, Solver};
    use crate::modeler::{HashableNodeRef, Node, NodeRef};
    use boolector_solver::{
        option::{BtorOption, ModelGen, OutputFileFormat},
        Btor, SolverResult, BV,
    };
    use std::collections::HashMap;
    use std::rc::Rc;

    type BVRef = BV<Rc<Btor>>;

    pub struct BoolectorSolver {
        solver: Rc<Btor>,
        mapping: HashMap<HashableNodeRef, BVRef>,
    }

    impl Solver for BoolectorSolver {
        fn name() -> &'static str {
            "Boolector"
        }

        fn new() -> Self {
            let solver = Rc::new(Btor::new());
            // TODO: Properly configure the below options.
            solver.set_opt(BtorOption::ModelGen(ModelGen::All));
            solver.set_opt(BtorOption::Incremental(true));
            solver.set_opt(BtorOption::OutputFileFormat(OutputFileFormat::SMTLIBv2));
            Self {
                solver,
                mapping: HashMap::new(),
            }
        }

        fn is_always_true(&mut self, node: &NodeRef) -> bool {
            let bv = self.visit(node).not();
            self.solve_impl(bv) == Solution::Unsat
        }

        fn is_always_false(&mut self, node: &NodeRef) -> bool {
            let bv = self.visit(node);
            self.solve_impl(bv) == Solution::Unsat
        }

        fn is_always_equal(&mut self, left: &NodeRef, right: &NodeRef) -> bool {
            let bv_left = self.visit(left);
            let bv_right = self.visit(right);
            let bv = bv_left._ne(&bv_right);
            self.solve_impl(bv) == Solution::Unsat
        }

        fn solve(&mut self, root: &NodeRef) -> Solution {
            let bv = self.visit(root);
            self.solve_impl(bv.slice(0, 0))
        }
    }

    impl BoolectorSolver {
        fn solve_impl(&mut self, bv: BVRef) -> Solution {
            self.solver.push(1);
            bv.assert();
            let solution = match self.solver.sat() {
                SolverResult::Sat => Solution::Sat,
                SolverResult::Unsat => Solution::Unsat,
                SolverResult::Unknown => Solution::Timeout,
            };
            self.solver.pop(1);
            solution
        }

        fn visit(&mut self, node: &NodeRef) -> BVRef {
            let key = HashableNodeRef::from(node.clone());
            self.mapping.get(&key).cloned().unwrap_or_else(|| {
                let value = self.translate(node);
                assert!(!self.mapping.contains_key(&key));
                self.mapping.insert(key, value.clone());
                value
            })
        }

        #[rustfmt::skip]
        fn translate(&mut self, node: &NodeRef) -> BVRef {
            match &*node.borrow() {
                Node::Const { sort, imm, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::from_u64(self.solver.clone(), *imm, width)
                }
                Node::Read { .. } => panic!("missing array logic"),
                Node::Write { .. } => panic!("missing array logic"),
                Node::Add { left, right, .. } => {
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    bv_left.add(&bv_right)
                }
                Node::Sub { left, right, .. } => {
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    bv_left.sub(&bv_right)
                }
                Node::Mul { left, right, .. } => {
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    bv_left.mul(&bv_right)
                }
                Node::Div { .. } => panic!("implement DIV"),
                Node::Rem { left, right, .. } => {
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    bv_left.urem(&bv_right)
                }
                Node::Ult { left, right, .. } => {
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    bv_left.ult(&bv_right)
                }
                Node::Ext { from, value, .. } => {
                    let width = from.bitsize() as u32;
                    let bv_value = self.visit(value);
                    assert_eq!(bv_value.get_width(), width);
                    bv_value.uext(64 - width)
                }
                Node::Ite { sort, cond, left, right, .. } => {
                    let width = sort.bitsize() as u32;
                    let bv_cond = self.visit(cond);
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    assert_eq!(bv_left.get_width(), width);
                    assert_eq!(bv_right.get_width(), width);
                    bv_cond.cond_bv(&bv_left, &bv_right)
                }
                Node::Eq { left, right, .. } => {
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    bv_left._eq(&bv_right)
                }
                Node::And { left, right, .. } => {
                    let bv_left = self.visit(left);
                    let bv_right = self.visit(right);
                    bv_left.and(&bv_right)
                }
                Node::Not { value, .. } => {
                    let bv_value = self.visit(value);
                    bv_value.not()
                }
                Node::State { init: None, sort, name, .. } => {
                    let width = sort.bitsize() as u32;
                    BV::new(self.solver.clone(), width, name.as_deref())
                }
                Node::State { init: Some(_), .. } => panic!("initialized"),
                Node::Next { .. } => panic!("should be unreachable"),
                Node::Input { .. } => panic!("should be unreachable"),
                Node::Bad { .. } => panic!("should be unreachable"),
                Node::Comment(_) => panic!("cannot translate"),
            }
        }
    }
}

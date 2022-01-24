use crate::modeler::Model;

//
// Public Interface
//

pub fn optimize_with_solver(_model: &mut Model) {
    #[cfg(feature = "boolector")]
    boolector_impl::optimize_with_boolector(_model)
}

//
// Private Implementation
//

#[cfg(feature = "boolector")]
mod boolector_impl {
    use crate::modeler::{get_bitsize, HashableNodeRef, Model, Node, NodeRef};
    use boolector_solver::{
        option::{BtorOption, ModelGen, OutputFileFormat},
        Btor, SolverResult, BV,
    };
    use log::{debug, warn};
    use std::collections::HashMap;
    use std::rc::Rc;

    pub fn optimize_with_boolector(model: &mut Model) {
        debug!("Optimizing model with 'Boolector' SMT solver ...");
        model.bad_states_initial.retain(should_retain_bad_state);
    }

    fn should_retain_bad_state(bad_state: &NodeRef) -> bool {
        if let Node::Bad { cond, name, .. } = &*bad_state.borrow() {
            let mut solver = BoolectorSolver::new();
            match solver.solve(cond) {
                Solution::Sat => {
                    warn!(
                        "Bad state '{}' is satisfiable!",
                        name.as_deref().unwrap_or("?")
                    );
                    true
                }
                Solution::Unsat => {
                    debug!(
                        "Bad state '{}' is unsatisfiable, removing",
                        name.as_deref().unwrap_or("?")
                    );
                    false
                }
                Solution::Timeout => {
                    warn!("Timeout not yet implemented!");
                    true
                }
            }
        } else {
            panic!("expecting 'Bad' node here");
        }
    }

    enum Solution {
        Sat,
        Unsat,
        Timeout,
    }

    type BVRef = BV<Rc<Btor>>;

    struct BoolectorSolver {
        solver: Rc<Btor>,
        mapping: HashMap<HashableNodeRef, BVRef>,
    }

    impl BoolectorSolver {
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

        fn solve(&mut self, root: &NodeRef) -> Solution {
            let bv = self.visit(root);
            bv.slice(0, 0).assert();
            match self.solver.sat() {
                SolverResult::Sat => Solution::Sat,
                SolverResult::Unsat => Solution::Unsat,
                SolverResult::Unknown => Solution::Timeout,
            }
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
                    let width = get_bitsize(sort) as u32;
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
                    let width = get_bitsize(from) as u32;
                    let bv_value = self.visit(value);
                    assert_eq!(bv_value.get_width(), width);
                    bv_value.uext(64 - width)
                }
                Node::Ite { sort, cond, left, right, .. } => {
                    let width = get_bitsize(sort) as u32;
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
                    let width = get_bitsize(sort) as u32;
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

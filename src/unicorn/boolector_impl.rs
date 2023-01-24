#[cfg(feature = "boolector")]
use crate::unicorn::smt_solver::{SMTSolution, SMTSolver};
#[cfg(feature = "boolector")]
use crate::unicorn::{HashableNodeRef, Node, NodeRef, NodeType};
#[cfg(feature = "boolector")]
use boolector_solver::{
    option::{BtorOption, ModelGen, OutputFileFormat},
    Array, Btor, SolverResult, BV,
};
#[cfg(feature = "boolector")]
use log::debug;
#[cfg(feature = "boolector")]
use std::collections::HashMap;
#[cfg(feature = "boolector")]
use std::rc::Rc;
#[cfg(feature = "boolector")]
use std::time::Duration;

#[cfg(feature = "boolector")]
type ArrayRef = Array<Rc<Btor>>;
#[cfg(feature = "boolector")]
type BitVectorRef = BV<Rc<Btor>>;

#[cfg(feature = "boolector")]
#[derive(Clone)]
enum BoolectorValue {
    BitVector(BitVectorRef),
    Array(ArrayRef),
}

#[cfg(feature = "boolector")]
pub struct BoolectorSolver {
    solver: Rc<Btor>,
    mapping: HashMap<HashableNodeRef, BoolectorValue>,
}

#[cfg(feature = "boolector")]
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
}

#[cfg(feature = "boolector")]
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
            Node::Or { left, right, .. } => {
                let bv_left = self.visit(left).into_bv();
                let bv_right = self.visit(right).into_bv();
                bv_left.or(&bv_right).into()
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
            Node::Bad { cond, .. } => {
                self.visit(cond)
            },
            Node::Comment(_) => panic!("cannot translate"),
        }
    }
}

#[cfg(feature = "boolector")]
impl From<BitVectorRef> for BoolectorValue {
    fn from(item: BitVectorRef) -> Self {
        Self::BitVector(item)
    }
}

#[cfg(feature = "boolector")]
impl From<ArrayRef> for BoolectorValue {
    fn from(item: ArrayRef) -> Self {
        Self::Array(item)
    }
}

#[cfg(feature = "boolector")]
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

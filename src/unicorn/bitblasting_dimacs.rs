use crate::unicorn::bitblasting::{GateModel, GateRef};
use crate::unicorn::cnf::{CNFBuilder, CNFContainer};
use crate::unicorn::{Node, NodeRef};
use anyhow::Result;
use std::io::Write;

//
// Public Interface
//

pub fn write_dimacs_model<W>(gate_model: &GateModel, out: W) -> Result<()>
where
    W: Write,
{
    let zip = gate_model
        .bad_state_nodes
        .iter()
        .zip(gate_model.bad_state_gates.iter());
    let mut dimacs = DimacsWriter::new();
    for (bad_state, gate) in zip {
        dimacs.convert_bad_state(bad_state, gate);
    }
    for (gate, val) in &gate_model.constraints {
        dimacs.convert_constraint(&gate.value, *val);
    }
    dimacs.write_dimacs(out)?;
    Ok(())
}

//
// Private Implementation
//

type Variable = u32;

#[derive(Clone)]
enum Literal {
    Var(Variable),
    Neg(Variable),
}

type Clause = Vec<Literal>;
type Formula = Vec<Clause>;

struct DimacsContainer {
    formula: Formula,
    variable_names: Vec<(Variable, String)>,
    current_var: Variable,
}

struct DimacsWriter {
    cnf_builder: CNFBuilder<DimacsContainer>,
    final_clause: Clause,
}

impl CNFContainer for DimacsContainer {
    type Variable = Variable;
    type Literal = Literal;

    fn new() -> Self {
        Self {
            formula: Vec::new(),
            variable_names: Vec::new(),
            current_var: 1,
        }
    }

    fn name() -> &'static str {
        "DIMACS"
    }

    fn var(var: Variable) -> Literal {
        Literal::Var(var)
    }

    fn neg(var: Variable) -> Literal {
        Literal::Neg(var)
    }

    fn new_var(&mut self) -> Variable {
        let var = self.current_var;
        self.current_var += 1;
        var
    }

    fn add_clause(&mut self, literals: &[Literal]) {
        self.formula.push(literals.to_vec());
    }

    fn record_variable_name(&mut self, var: Self::Variable, name: String) {
        self.variable_names.push((var, name));
    }

    fn record_input(&mut self, _var: Self::Variable, _gate: &GateRef) {}
}

impl DimacsWriter {
    fn new() -> Self {
        Self {
            cnf_builder: CNFBuilder::<DimacsContainer>::new(),
            final_clause: Vec::new(),
        }
    }

    fn cnf(&self) -> &DimacsContainer {
        self.cnf_builder.container()
    }

    fn cnf_mut(&mut self) -> &mut DimacsContainer {
        self.cnf_builder.container_mut()
    }

    fn convert_bad_state(&mut self, bad_state: &NodeRef, gate: &GateRef) {
        let bad_state_var = self.cnf_builder.visit(gate);
        if let Node::Bad { name, .. } = &*bad_state.borrow() {
            let name = name.as_deref().unwrap_or("?").to_string();
            self.cnf_mut().record_variable_name(bad_state_var, name);
            self.final_clause.push(Literal::Var(bad_state_var));
        } else {
            panic!("expecting 'Bad' node here");
        }
    }

    fn convert_constraint(&mut self, gate: &GateRef, val: bool) {
        let constraint_variable = self.cnf_builder.visit(gate);
        let constraint_literal = if val {
            Literal::Var(constraint_variable)
        } else {
            Literal::Neg(constraint_variable)
        };
        self.cnf_mut().add_clause(&[constraint_literal]);
    }

    fn write_clause<W: Write>(&self, clause: &[Literal], mut out: W) -> Result<()> {
        for literal in clause {
            match literal {
                Literal::Var(x) => write!(out, "{} ", x)?,
                Literal::Neg(x) => write!(out, "-{} ", x)?,
            }
        }
        writeln!(out, "0")?;
        Ok(())
    }

    fn write_dimacs<W: Write>(&self, mut out: W) -> Result<()> {
        let num_bad = self.final_clause.len();
        let num_names = self.cnf().variable_names.len();
        let num_clauses = self.cnf().formula.len() + 1;
        let num_vars = self.cnf().current_var - 1;
        writeln!(out, "c cksystemsgroup.github.io/unicorn")?;
        writeln!(out, "c CNF contains a total of {} clauses.", num_clauses)?;
        writeln!(out, "c CNF contains a total of {} variables.", num_vars)?;
        writeln!(out, "c CNF clauses cover {} bad states.", num_bad)?;
        writeln!(out, "c Variable name mapping ({} names):", num_names)?;
        for (variable, name) in self.cnf().variable_names.iter() {
            writeln!(out, "c   {}: {}", variable, name)?;
        }
        writeln!(out, "p cnf {} {}", num_vars, num_clauses)?;
        for clause in self.cnf().formula.iter() {
            self.write_clause(clause, &mut out)?;
        }
        self.write_clause(&self.final_clause, &mut out)?;
        Ok(())
    }
}

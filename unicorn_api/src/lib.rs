use std::{path::PathBuf, cell::RefCell};

use pyo3::{prelude::*, types::PyDict};
use riscu::load_object_file;
use unicorn::{unicorn::{quarc::{QuantumCircuit, Unitary, QubitRef, get_constant, get_qubit_dependecy, get_dependency_data}, builder::generate_model, btor2file_parser::parse_btor2_file, memory::replace_memory, unroller::{unroll_model, prune_model, renumber_model}, optimize::optimize_model}};
use bytesize::ByteSize;
use unicorn::unicorn::z3solver_impl;
use std::collections::HashMap;
use unicorn::unicorn::quarc::HashableDependencyRef;

struct PyDependency {
    // each dependency has a unique id
    id: u64, 
    //  is either "div" or "rem"
    name: String,
    // there should be only two operands
    operands: Vec<Vec<QubitRef>>, 
}

#[doc(hidden)]
impl PyDependency {
    pub fn new(id: u64, name: &String, operands: &Vec<Vec<QubitRef>>) -> Self {
        Self{
            id, 
            name: name.to_string(),
            operands: operands.to_vec()
        }
    }
}

#[doc(hidden)]
impl ToPyObject for PyDependency {
    // return a valid Python object
    fn to_object(&self, py: Python<'_>) -> PyObject {

        let dict = PyDict::new(py);
        let _ = dict.set_item("id", self.id.to_object(py));
        let _ =dict.set_item("name", self.name.to_object(py));
        let mut operands : Vec<Vec<PyQubit>> = Vec::new();
        for operand in self.operands.iter() {
            operands.push(get_pyqubit_vec(operand));
        }

        let _ = dict.set_item("target", operands.to_object(py));
        dict.to_object(py)
    }
}


struct PyQubit {
    // In Python interface you can access each of this elements as if a dictionary: qubit["id"] or qubit["dependency"].
    // each qubit has a unique id. Also, division and remainder create dependecies. Qubits that have a dependency should be initialized to |+>.
    id: u64, 
    dependency: Option<PyDependency>
}

#[doc(hidden)]
impl PyQubit {
    pub fn new(qubit: &QubitRef) -> Self {
        let id;
        if let Some(val) = get_constant(qubit) {
            if val {
                id = 1;
            } else {
                id = 0;
            }
        } else {
            id = RefCell::as_ptr(qubit) as u64;
        }

        let dep_ = get_qubit_dependecy(qubit);
        let pydep = if let Some(dep) = dep_ {
            Some(PyDependency::new(dep.0, &dep.1, &dep.2))
        } else {
            None
        };

        Self{
            id: id,
            dependency: pydep
        }
    }
}

#[doc(hidden)]
impl ToPyObject for PyQubit {
    // return a valid Python object
    fn to_object(&self, py: Python<'_>) -> PyObject {
        let dict = PyDict::new(py);
        let _ =dict.set_item("id", self.id.to_object(py));
        let _ = dict.set_item("dependency", self.dependency.to_object(py));
        dict.to_object(py)
    }
}


struct PyQuantumGate {
    // Quantum gates are represented in terms of controls and target, for X gates only the target is set.
    controls: Vec<PyQubit>,
    target: PyQubit 
}

#[doc(hidden)]
impl ToPyObject for PyQuantumGate {
    fn to_object(&self, py: Python<'_>) -> PyObject {
        let dict = PyDict::new(py);
        let _ =dict.set_item("controls", self.controls.to_object(py));
        let _ = dict.set_item("target", self.target.to_object(py));
        dict.to_object(py)
    }
}

#[doc(hidden)]
fn get_pyqubit_vec(qubits: &[QubitRef]) -> Vec<PyQubit> {
    // given a vector of qubits in rust, we return a vector of qubits for Python
    let mut answer = vec![];
    for qubit in qubits.iter() {
        answer.push(PyQubit::new(qubit));
    }
    answer
}

#[doc(hidden)]
impl PyQuantumGate {
    pub fn new(controls_: &[QubitRef], target_: &QubitRef) -> Self {
        Self{
            controls: get_pyqubit_vec(controls_),
            target: PyQubit::new(target_)
        }
    }
}


struct PyQuantumCircuit {
    circuit_stack: Vec<PyQuantumGate>,
    input_qubits: Vec<PyQubit>,
    dependencies: HashMap<HashableDependencyRef, Vec<QubitRef>>,
    oracle_output: PyQubit
}

#[doc(hidden)]
impl PyQuantumCircuit {
    pub fn new(circuit_stack: Vec<PyQuantumGate>, input_qubits: &[QubitRef], oracle_output: &QubitRef, dependencies: HashMap<HashableDependencyRef, Vec<QubitRef>>) -> Self {
        Self{
            // a vector of PyQuantumGates (only NOTs and CNOTs)
            circuit_stack, 
            // ids of the qubits that are the inputs of the quantum circuit
            input_qubits: get_pyqubit_vec(input_qubits), 
             // the id of the qubit that represents the outputs of oracle
            oracle_output: PyQubit::new(oracle_output),
            // maps a Dependency -> what set of qubits it solves in LSB
            dependencies 
        }
    }
}

impl ToPyObject for PyQuantumCircuit {
    fn to_object(&self, py: Python<'_>) -> PyObject {

        let dependencies = PyDict::new(py);
        for (key, value) in self.dependencies.iter() {
            let target = get_pyqubit_vec(value);
            let (id, name, operands) = get_dependency_data(key);
            let _ = dependencies.set_item(PyDependency::new(id, &name, &operands), target);
            
        }

        let dict = PyDict::new(py);
        let _ =dict.set_item("circuit_stack", self.circuit_stack.to_object(py));
        let _ = dict.set_item("input_qubits", self.input_qubits.to_object(py));
        let _ = dict.set_item("oracle_output", self.oracle_output.to_object(py));
        let _ = dict.set_item("dependencies", dependencies);
        dict.to_object(py)
    }
}

#[pyfunction]
fn get_qc_from_binary(path: String, unroll: usize, max_heap: u32, max_stack: u32, memory_size_: u64) -> Py<PyAny> {
    // returns PyQuantumCircuit
    let input = PathBuf::from(path.clone());
    let memory_size = ByteSize::mib(memory_size_).as_u64();
    let prune = true;
    let extras = ["--fast-minimize".to_string(), "-p".to_string()].to_vec();

    let model = {
        let mut model = if true {
            let program = load_object_file(&input).expect("could not load object file");
            let argv = [vec![path], extras].concat();
            generate_model(&program, memory_size, max_heap, max_stack, &argv).expect("error generating model")
        } else {
            parse_btor2_file(&input)
        };

        
        model.lines.clear();
        replace_memory(&mut model);
        for n in 0..unroll {
            unroll_model(&mut model, n);
        }
        if prune {
            prune_model(&mut model);
        }
        
        optimize_model::<z3solver_impl::Z3SolverWrapper>(&mut model);
        renumber_model(&mut model);
        Some(model)
    };

    
    let m = model.unwrap();
    let mut qc = QuantumCircuit::new(&m, 64); // 64 is a paramater describing wordsize
    let _ = qc.process_model(1);

    let mut py_circuit_stack: Vec<PyQuantumGate> = vec![];


    for gate in qc.circuit_stack.iter() {
        match &*gate.as_ref().borrow() {
            Unitary::Not { input } => {
                py_circuit_stack.push(PyQuantumGate::new(&vec![], input));
            },
            Unitary::Cnot { control, target } => {
                py_circuit_stack.push(PyQuantumGate::new(&vec![control.clone()], target));
            },
            Unitary::Mcx {
                controls,
                target,
            } => {
                py_circuit_stack.push(PyQuantumGate::new(controls, target));
            },
            Unitary::Barrier => {} 
        }
    
    }

    let mut input_qubits = vec![];

    for (_, qubit) in qc.input_qubits.iter() {
        input_qubits.extend(qubit.clone());
    }

    

    Python::with_gil(|py| {
        PyQuantumCircuit::new(py_circuit_stack, &input_qubits, &qc.output_oracle.unwrap(), qc.dependencies).to_object(py)
    })
}

// A Python module implemented in Rust.
#[pymodule]
fn unicorn_api(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(get_qc_from_binary, m)?)?;
    Ok(())
}
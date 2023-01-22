# Unicorn API
You will need to install [maturin](https://www.maturin.rs/installation.htm) and create a virtual environment in Python. Finally, just type `maturin develop` to install the unicorn API in your virtual environment. 

To generate additional documentation type `cargo doc`.

## QUARC

Note: This tutorials assume you are in `unicorn_api/` directory. Additionally, our integer representation at bit level is LSB.

### Some Objects

```rust
// all these objects are dictionaries when used in Python

struct PyQubit {
    // each qubit has a unique id. Also, division and remainder create dependecies. Qubits that have a dependency should be initialized to |+>.
    id: u64, 
    dependency: Option<PyDependency>
}

struct PyQuantumGate {
    // Quantum gates are represented in terms of controls and target. For X gates only the target is set.
    controls: Vec<PyQubit>,
    target: PyQubit 
}

struct PyDependency {
    id: u64, /// each dependency has a unique id
    name: String,///  is either "div" or "rem"
    operands: Vec<Vec<QubitRef>>, /// there should be only two operands
}

```
### Building a quantum circuit from a binary

We can build an optimized quantum oracle by doing:

```Python
from unicorn_api import get_qc_from_binary

# it uses z3 to optimize the circuit
quantum_circuit = get_qc_from_binary("../examples/selfie/d.m", # path to the binary
                                    86, # number of state transitions
                                    8, # Max number of words that the HEAP can use
                                    32, # Max number of words that the STACK can use
                                    1) # Memory size in MiB
oracle_output = quantum_circuit["oracle_output"] # id of the qubit that represents the oracle output

circuit_stack = quantum_circuit["circuit_stack"] # This is a vector of PyQuantumGates. When uncomputing, you may want to uncompute all gates but the last one since this is the one that affects the oracle's output.

input_qubits = quantum_circuit["input_qubits"] # this is a vector of integers, that contain the ids of the qubits that represent the input of the program and the ones we want to search for.

dependencies = quantum_circuit["dependencies"] # Division and remainder are stated as constraints and this is a dictionary that maps PyDependency -> Vec<PyQubit>. By solving, this specific PyDependency the value of Vec<PyQubit> can be determined.

```



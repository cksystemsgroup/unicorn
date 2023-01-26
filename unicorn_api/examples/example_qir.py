from typing import Dict, List
from unicorn_api import get_qc_from_binary
import pyqir
from utils_qir import *
from math import ceil

def get_pyqir_grover(path: str, unroll: int, max_heap: int = 8, max_stack: int = 32, memory_size: int = 1) :
    '''
    It created a QIR module of grover algorithm to search for bad-states in the file specified by path
    This function returns:
    1. A module that is the oracle 
    2. A List of IDs of qubits which are the input we must search using Grover Algorithm
    '''

    quantum_circuit_data = get_qc_from_binary(path, unroll, max_heap, max_stack, memory_size)
    circuit_stack = quantum_circuit_data["circuit_stack"]
    input_qubits = quantum_circuit_data["input_qubits"]
    dependencies = quantum_circuit_data["dependencies"]

    # since PyQIR does not yet implements arbitrary MCX gates we will implement it from scratch using ancilla_max_count ancillas at most.
    max_controls_in_circuit = get_max_controls_in_gates(circuit_stack)
    ancillas_mcx_count = max_controls_in_circuit - 2

    # get a dictionary (mapping_ids) that maps QIR module qubit indices to the ids the unicorn outputs. Instead, ancilla_qir_indices, are the indices used in QIR module for ancillas in MCX gates
    mapping_ids, ancilla_qir_indices = init_vars(quantum_circuit_data, ancillas_mcx_count)
    oracle_id = mapping_ids[quantum_circuit_data["oracle_output"]["id"]]

    # some checks
    count_input  = len(input_qubits) + len(dependencies)
    last_gate = circuit_stack[len(circuit_stack)-1]
    last_gate_controls_ids = get_vec_local_ids(mapping_ids, last_gate["controls"])
    print("last gate controls ", len(last_gate_controls_ids))
    for c in last_gate_controls_ids:
        assert(oracle_id != c)
    last_gate_target = mapping_ids[last_gate["target"]["id"]]
    print(last_gate_target, oracle_id)
    assert(last_gate_target == oracle_id)
    # ------------------------------------------

    # init QIR module
    module = pyqir.SimpleModule(f"grover({path})", num_qubits=len(mapping_ids.keys()) + ancillas_mcx_count, num_results=len(input_qubits))
    qis = pyqir.BasicQisBuilder(module.builder)

    void = pyqir.Type.void(module.context)
    ccx_function = module.add_external_function("ccx", pyqir.FunctionType(void, [pyqir.qubit_type(module.context), pyqir.qubit_type(module.context), pyqir.qubit_type(module.context)]))
    

    # GROVER algorithm starts here

    # initialize input qubits to |+>
    all_inputs = []
    for qubit in get_vec_local_ids(mapping_ids, input_qubits):
        all_inputs.append(qubit)
        qis.h(module.qubits[qubit])
    for target_qubits in dependencies.values():
        for qubit in get_vec_local_ids(target_qubits):
            all_inputs.append(qubit)
            qis.h(module.qubits[qubit])

    # initialize  oracle_output to |->
    qis.x(module.qubits[oracle_id])
    qis.h(module.qubits[oracle_id])

    for _ in range(ceil(2**(count_input/2))):

        # apply oracle
        for gate in circuit_stack:
            controls = get_vec_local_ids(mapping_ids, gate["controls"])
            qir_apply_gate(qis, module, controls, mapping_ids[gate["target"]["id"]], ancilla_qir_indices, ccx_function)

        # uncompute oracle, without uncomputing the oracle's output
        for gate in circuit_stack[len(circuit_stack)-2::-1]:
            controls = get_vec_local_ids(mapping_ids, gate["controls"])
            for c in controls:
                assert(c != oracle_id)
            target = mapping_ids[gate["target"]["id"]]
            qir_apply_gate(qis, module, controls, target, ancilla_qir_indices, ccx_function)

        # apply inversion above average procedure
        for qubit in all_inputs:
            qis.h(module.qubits[qubit])
            qis.x(module.qubits[qubit])

        # multi-controlled Z
        qis.h(module.qubits[all_inputs[0]])
        apply_mcx_gate(qis, module, all_inputs[1:], all_inputs[0], ancilla_qir_indices, ccx_function)
        qis.h(module.qubits[all_inputs[0]])

        # apply inversion above average procedure
        for qubit in all_inputs:
            qis.h(module.qubits[qubit])
            qis.x(module.qubits[qubit])

    # measure result
    for (index, qubit) in enumerate(input_qubits):
        qis.mz(module.qubits[mapping_ids[qubit["id"]]], module.results[index])

    return module.ir()

print("file: d.m")
qir_ir = get_pyqir_grover("../../examples/selfie/d.m", 84)
file = open("d.qir", "w")
file.write(qir_ir)
file.close()


from typing import Dict, List, Tuple, Any
from pyqir import BasicQisBuilder, SimpleModule

def get_vec_local_ids(mapping_ids: Dict[int, int], qubits: List[Dict]) -> List[int]:
    '''
    returns a vector of QIR indices used in the a module, where mapping ids maps QUARC qubit's ids to QIR indices.
    '''
    ans = []
    for qubit in qubits:
        ans.append(mapping_ids[qubit["id"]])
    return ans

def insert_new_id(mapping_ids: Dict[int, int], local_id: int, id: int) -> Tuple[bool, int]:
    ''''
    mapping_ids map a QUARC qubit's id to a indices in a QIR module. This function updates mapping_ids to contain local_id (QIR index).
    '''
    print(id)
    if id in mapping_ids.keys():
        return False, local_id
    else:
        mapping_ids[id] = local_id
        return True, local_id + 1

def init_vars(quantum_circuit_data: Dict[str, Any], ancillas_mcx_count: int) -> Tuple[Dict[int, int], List[int]]:
    '''
    returns: 
    - mapping_ids: maps QUARC qubit's ids to the indices used in QIR module
    - ancillas_ids: a list of QIR indices used for MCX gates
    '''
    local_id = 2
    mapping_ids = dict({0: 0, 1: 1})

    input_qubits = quantum_circuit_data["input_qubits"]
    for qubit in input_qubits:
        _, local_id = insert_new_id(mapping_ids, local_id, qubit['id'])

    ancillas_ids = []
    for _ in range(ancillas_mcx_count):
        ancillas_ids.append(local_id)
        local_id += 1

    oracle_output = quantum_circuit_data["oracle_output"]["id"]
    _, local_id = insert_new_id(mapping_ids, local_id, oracle_output)
    circuit_stack = quantum_circuit_data["circuit_stack"]
    for gate in circuit_stack:
        for c in gate["controls"]:
            _, local_id = insert_new_id(mapping_ids, local_id, c["id"])
        _, local_id, insert_new_id(mapping_ids, local_id, gate["target"]["id"])
    return mapping_ids, ancillas_ids

def get_max_controls_in_gates(circuit_stack) -> int:
    '''
    given a circuit stack it returns the maximum number of controls in all gates.
    '''
    answer = 0
    for gate in circuit_stack:
        answer = max(answer, len(gate["controls"]))
    return answer

def apply_mcx_gate(qis: BasicQisBuilder, module: SimpleModule, controls: List[int], target: int, ancilla_indices: List[int]):
    '''
    tries to apply an MCX gate with arbitrary controls.
    '''
    if len(controls) == 0:
        raise Exception("MCX gates cannot be applied with 0 controls")
    elif len(controls) == 1:
        qis.cx(module.qubits[controls[0]], module.qubits[target])
    elif len(controls) == 2:

        qis.ccx(qis._builder, module.qubits[controls[0]], module.qubits[controls[1]], module.qubits[target])
    else:
        # this is a custom MCX gate
        current_ancilla = 0
        qis.ccx(qis._builder, module.qubits[controls[0]], module.qubits[controls[1]], module.qubits[ancilla_indices[current_ancilla]])
        current_ancilla += 1

        to_reverse = []
        for i in range(2, len(controls)-1):
            qis.ccx(qis._builder, module.qubits[controls[i]], 
                    module.qubits[ancilla_indices[current_ancilla-1]], 
                    module.qubits[ancilla_indices[current_ancilla]])
            to_reverse.append([controls[i], ancilla_indices[current_ancilla-1], ancilla_indices[current_ancilla]])
            current_ancilla += 1

        qis.ccx(qis._builder, module.qubits[controls[i]], 
                module.qubits[ancilla_indices[current_ancilla-1]], 
                module.qubits[target])

        # free up ancillas
        for gate in to_reverse[::-1]:
            qis.ccx(qis._builder, module.qubits[gate[0]],module.qubits[gate[1]], module.qubits[gate[2]])


def qir_apply_gate(qis: BasicQisBuilder, module: SimpleModule, controls: List[int], target: int, ancilla_indices: List[int]) :
    if len(controls) == 0:
        qis.x(module.qubits[target])
    elif len(controls) == 1:
        apply_mcx_gate(qis, module, controls, target, ancilla_indices)

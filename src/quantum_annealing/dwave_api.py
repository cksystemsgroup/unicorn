from dwave.system import DWaveSampler, EmbeddingComposite
from greedy import SteepestDescentComposite
from dimod import BinaryQuadraticModel, Vartype
import math

def sample_qubo(*args, **kwargs):
    print(kwargs)
    file = open(kwargs["path"])
    section = 1
    bqm = BinaryQuadraticModel(Vartype.BINARY)
    inputs = {}
    bad_states = {}
    fixed_qubits = {}
    for line in file.readlines():
        if line == '\n':
            section+=1
        else:
            elements = line[:-1].split(" ")
            if section == 1:
                bqm.offset = float(elements[1])
            elif section == 2:
                qubit_names = [int(x) for x in elements[1].split(",")]
                qubit_values = elements[2].split(",")
                for i in range(len(qubit_values)):
                    if qubit_values[i] != "-":
                        fixed_qubits[qubit_names[i]] = int(qubit_values[i])
                inputs[elements[0]] =  qubit_names
            elif section == 3:
                bad_states[elements[0]] = int(elements[1])
                if elements[2] != "-":
                    fixed_qubits[int(elements[1])] = int(elements[2])
            elif section == 4:
                bqm.add_variable(int(elements[0]), float(elements[1]))
            elif section == 5:
                var1 = int(elements[0])
                var2 = int(elements[1])
                bqm.add_variable(var1)
                bqm.add_variable(var2)
                bqm.add_interaction(var1, var2, float(elements[2]))
            else:
                raise Exception("Error in parsing unicorn file. This should not be reachable code.")
    file.close()

    
    qpu = EmbeddingComposite(DWaveSampler(solver={"name": "Advantage_system4.1"}))
    sampler = SteepestDescentComposite(qpu)
    result = sampler.sample(bqm, num_reads=int(kwargs["num_reads"]), chain_strength=float(kwargs["chain_strength"])).first
    print("final offset: ", result.energy)
    print()

    variables_result = result[0]

    for (nid, variables) in inputs.items():
        binary_form = ""
        decimal = 0
        for i in range(len(variables)):
            qubit = variables[i]
            if qubit in fixed_qubits:
                value = fixed_qubits[qubit]
            else:
                value = variables_result[qubit]
            decimal += value*math.pow(2,i)
            binary_form+=str(value)
        print("input: ", nid, decimal, binary_form[::-1])
    print()
    print("True bad states nids")
    true_bad_nid_found = False
    for (nid, qubit) in bad_states.items():
        if qubit in fixed_qubits:
            if fixed_qubits[qubit]:
                print("Bad state:", nid)
                true_bad_nid_found = True
        elif variables_result[qubit]:
            print("Bad state:", nid)
            true_bad_nid_found = True
    if not true_bad_nid_found:
        print("not bad states occur")


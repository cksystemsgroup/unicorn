[![Unitary Fund](https://img.shields.io/badge/Supported%20By-UNITARY%20FUND-brightgreen.svg?style=for-the-badge)](http://unitary.fund)

# Unicorn: Symbolic Execution, Bounded Model Checker and Code Optimization of C Programs on Quantum Computers

[![Build Status](https://img.shields.io/github/workflow/status/cksystemsgroup/unicorn/Test)](https://github.com/cksystemsgroup/unicorn/actions)
![Experimental Status](https://img.shields.io/badge/status-experimental-yellow.svg)
![Rust Version](https://img.shields.io/badge/Rust-v1.57.0-yellow)
![Platform](https://img.shields.io/badge/platform-linux%20%7C%20macos%20%7C%20windows-brightgreen)
[![Lines of Code](https://img.shields.io/tokei/lines/github/cksystemsgroup/unicorn)](https://github.com/cksystemsgroup/unicorn)
[![License](https://img.shields.io/github/license/cksystemsgroup/unicorn)](https://github.com/cksystemsgroup/unicorn/blob/master/LICENSE)

Symbolic execution and bounded model checking involves solving a very computationally-expensive problem. This is why we created unicorn, and interface for the best classical and quantum algorithms to meet, and determine the input(s) that make programs run into specific machines states. 

Unicorn compiles 64-bit RISC-V ELF binaries to quantum circuits and ISING-hamiltonians that can run on both gate-model and adiabatic-based quantum computers. Quantum circuits are done by QUARC, and the hamiltonians are built by QUBOT. QUARC is still on its way, and only a non-optimized prototype written in Python exists.

Unicorn models RISC-V code execution with a bit-precise finite state machine over all RISC-V machine states using 64-bit bitvectors, one for each general-purpose 64-bit CPU register, 1-bit bitvectors, one for each possible program counter value, and an array of 64-bit bitvectors modeling 64-bit main memory.

Unicorn constructs the finite state machine such that a state `S` is reachable from the initial state in `n` state transitions if and only if there is input to the RISC-V code that makes a RISC-V machine reach the machine state modeled by `S` after executing the RISC-V code for no more than `n` instructions.

Unicorn outputs the finite state machine for a given state `S` either as objective function of a quantum annealer for a given bound on `n`, or as quantum circuit for a quantum computer and unbounded `n`. Thus the output of a quantum machine is an input to the RISC-V code for reaching `S` during execution, if there is such input, resembling what a symbolic execution engine and bounded model checker for RISC-V would do.

Unicorn reports the size of objective functions and quantum circuits in number of quantum bits. Objective functions grow linearly in `n` (quadratically in `n` if the RISC-V code's memory consumption is unbounded). Quantum circuits grow linearly in code size (memory usage if the RISC-V code's memory consumption is unbounded).

Unicorn optimizes size by applying SMT and SAT solvers during compilation. Whenever a quantum bit can be shown to represent a constant value for all inputs, the bit is replaced with that value. Given a time budget `T`, unicorn attempts to find solutions for all quantum bits within `T`. Only if unicorn runs out of time, involving a quantum machine makes sense yet only as long as the number `u` of undetermined quantum bits is less than the number `a` of quantum bits available on the machine. We call `a-u` the quantum advantage with time budget `T`.

Unicorn supports a subset of 64-bit and 32-bit RISC-V called RISC-U, where the U stands for unsigned integer arithmetic, and five system calls (`exit`, `brk`, `openat`, `read`, `write`). RISC-U code gets input through the `read` system call. We plan to support all of RISC-V and more system calls eventually.

For more information on how unicorn works check out our [paper](https://arxiv.org/abs/2111.12063).

### Toolchain Setup
Unicorn can be build and run on all major platforms.
Just make sure you build for one of these targets:
 - x86_64-unknown-linux-gnu
 - x86_64-apple-darwin
 - x86_64-pc-windows-msvc

1. Bootstrap Rust v1.57.0 from [https://rustup.rs](https://rustup.rs) and make sure:
 - you install it with one of the supported host triples and 
 - add it to your path
2. Install Rustfmt (formatter) and Clippy (linter)
```sh
$ rustup component add rustfmt
$ rustup component add clippy
```
3. Install tool for documentation generation
```sh
$ cargo install mdbook --locked
$ cargo install mdbook-linkcheck --locked
$ cargo install mdbook-graphviz --locked
```

### Build and Test from Source
Tests can be executed on all platforms, alltough one
feature is not supported on Windows: `boolector`

1. Test your toolchain setup by compiling monster:
```sh
$ cargo build --locked
```
2. Execute tests:
```sh
$ cargo test --locked
```
## Usage

First, generate a RISC-U binary with [Selfie](https://github.com/cksystemsteaching/selfie) using the command below:

```sh
selfie -c <SOURCE_CODE_FILE> -o <BINARY_FILE>
```

To display the available subcommands that Unicorn has you can type `./target/debug/unicorn --help`, or to display subcommand options `./target/debug/unicorn <SUBCOMMAND> --help`.

Currently, there are 3 main commands:
### 1. Generate a BTOR2 file from a binary
```sh
./target/debug/unicorn beator <BINARY_FILE> --unroll <NUM_STATE_TRANSITIONS> --solver boolector --out <BTOR2_FILE>
```
The above command generates a BTOR2 file, while the unroll option specifies how many state transitions Unicorn should represent in the BTOR2 file. In this example, Unicorn optimizes the number of variables using Boolector. 

There are more options. For example, you can add `--bitblast` to the command, and the BTOR2 file will represent a logic (combinatorial) circuit.


### 2. Generate and/or test a QUBO of the binary
```sh
./target/debug/unicorn qubot <BINARY_FILE> --unroll <NUM_STATE_TRANSITIONS> --solver <SMT_SOLVER> --out <QUBO_FILE> --inputs 42,32;34
```
This command dumps a QUBO model in `<QUBO_FILE>`, however passing `--out` is optional.

The `--inputs` parameter is also optional. In this example, we are assuming our model consumes two inputs. Therefore, we are first testing our model with inputs 42 and 32, and then 34 (the first value of each test is replicated to satisfy the number of inputs the model consumes if there are not enough values). 

In this example, Unicorn prints one line for each test in the terminal:

```sh
offset:2, bad states count:0
offset:0, bad states count:1
```

For the first test, our model does not reach a ground state, therefore no bad state happens. However, the second line tells us that input 32 makes one bad state reachable.

The QUBO file has five sections, each section is separated by an empty line, and each line separates values by a space. The file is described as follows:

1. The first section consists of a single line, and it contains two numbers: the number of variables and the offset of the QUBO. 
2. The second section contains lines mapping input-nids of the corresponding BTOR2 file to unique identifiers of qubits, and whether or not our optimization techniques found some value for each of the qubits. IDs of qubits are separated by commas (LSB comes first), and `-` means that the SMT/SAT solvers have not determined a value for these qubits.
3. The third section is similar to the previous one, but instead, it maps bad-state-nids to qubits ids. Bad states are booleans, therefore only one qubit-id is needed.
4. The fourth section describes linear coefficients and follows the format `<qubit-id> <linear-coeff>`.
5. The last section describes quadratic (bilinear) coefficients and follows the format `<qubit-id> <qubit-id> <quadratic-coeff>`.

Here you can see an example of what the file might look like:

```
548 1023

10000001 1,2,3,4,5,6,7,8 -,-,-,-,-,-,-,-

10000148 13 0
10000148 14 -

9 2
10 0
11 0
12 4
...

1 9 4
3 9 6
...
```
### 3. Execute a QUBO file on real quantum hardware
Right now, we are wrapping Python functions to access real hardware, and the implementation of embedding algorithm and a REST framework is still on its way.

To execute on real quantum hardware, first, refer to this [setup guide](https://docs.ocean.dwavesys.com/en/latest/overview/install.html#set-up-your-environment).

The command below performs `<NUM_RUNS>` samples on the quantum annealer, while the physical qubits will have an absolute coupling value of `CHAIN_STRENGTH`.

```sh
./target/debug/unicorn dwave <QUBO_FILE> --num-runs <NUM_RUNS> --chain-strength <CHAIN_STRENGTH>
```

Running this command will output on the terminal: 

1. The minimum energy (final offset of the QUBO) that the annealer found among all runs.
2. One line for each input nid that the model has. Unicorn displays for each input a nid, a value in decimal, and a value in binary (MSB).
3. The nids of the bad states that occur (qubits whose value are 1).

Below is an example of a small QUBO file representing an AND gate, and the output for such file:

```
3 0

1 1,2 -,-

bad 3 -

3 6

1 2 2
1 3 -4
2 3 -4
```

``` sh
Py(0x10cdd90d0)
{'path': 'and.unicorn', 'num_reads': '10', 'chain_strength': '1'}
final offset:  0.0

input:  1 2.0 10

True bad states nids
no bad states occur
```

## License

Copyright (c) 2022. The Unicorn Authors. All rights reserved.

Licensed under the [MIT](LICENSE) license.

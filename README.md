# Unicorn: A Compiler and Runtime System for Quantum Computing

[![Build Status](https://img.shields.io/github/workflow/status/cksystemsgroup/monster/Test)](https://github.com/cksystemsgroup/monster/actions)
[![Crate](https://img.shields.io/crates/v/monster-rs.svg)](https://crates.io/crates/monster-rs)
[![API](https://docs.rs/monster-rs/badge.svg)](https://docs.rs/monster-rs)
![Experimental Status](https://img.shields.io/badge/status-experimental-yellow.svg)
![Rust Version](https://img.shields.io/badge/Rust-v1.57.0-yellow)
![Platform](https://img.shields.io/badge/platform-linux%20%7C%20macos%20%7C%20windows-brightgreen)
[![Lines of Code](https://img.shields.io/tokei/lines/github/cksystemsgroup/monster)](https://github.com/cksystemsgroup/monster)
[![License](https://img.shields.io/crates/l/monster-rs)](https://github.com/cksystemsgroup/monster/blob/master/LICENSE)

Unicorn compiles 64-bit RISC-V ELF binaries to quantum circuits and objective functions that run on quantum computers and quantum annealers, respectively, with a possibly exponential advantage.

Unicorn models RISC-V code execution with a bit-precise finite state machine over all RISC-V machine states using 64-bit bitvectors, one for each general-purpose 64-bit CPU register, 1-bit bitvectors, one for each possible program counter value, and an array of 64-bit bitvectors modeling 64-bit main memory.

Unicorn constructs the finite state machine such that a state S is reachable from the initial state in n state transitions if and only if there is input to the RISC-V code that makes a RISC-V machine reach the machine state modeled by S after executing the RISC-V code for no more than n instructions.

Unicorn outputs the finite state machine for a given state S either as objective function of a quantum annealer for a given bound on n, or as quantum circuit for a quantum computer and unbounded n. Thus the output of a quantum machine is input to the RISC-V code for reaching S, if there is such input.

Unicorn reports the size of objective functions and quantum circuits in number of quantum bits. Objective functions grow linearly in n (quadratically in n if the RISC-V code's memory consumption is unbounded). Quantum circuits are linear in code size (linear in memory size if the RISC-V code's memory consumption is unbounded).

Unicorn optimizes size by applying SMT and SAT solvers during compilation.

For more information about our work you can check our [paper](https://arxiv.org/abs/2111.12063).

### Toolchain Setup
Monster can be build and tested on all major platforms.
Just make sure you build for one of these targets:
 - x86_64-unknown-linux-gnu
 - x86_64-apple-darwin
 - x86_64-pc-windows-msvc

1. Bootstrap Rust v1.57.0 from [https://rustup.rs](https://rustup.rs) and make sure:
 - you install it with one of the supported host triples and 
 - add it to your path
2. Install Rustfmt (formatter) and Clippy (linter)
```
$ rustup component add rustfmt
$ rustup component add clippy
```
3. Install tool for documentation generation
```
$ cargo install mdbook --locked
$ cargo install mdbook-linkcheck --locked
$ cargo install mdbook-graphviz --locked
```

### Build and Test from Source
Tests can be executed on all platforms, alltough one
feature is not supported on Windows: `boolector`

1. Test your toolchain setup by compiling monster:
```
$ cargo build --locked
```
2. Execute tests:
```
$ cargo test --locked
```
## Usage

First, generate a RISC-U binary (full support of RISC-V is coming soon!). Refer to the [selfie repository](https://github.com/cksystemsteaching/selfie). Once selfie is installed you can generate a binary for code you have written in a file (e.g `hello.c`):

```
selfie -c hello.c -o hello.m
```

To display the available subcommands that Unicorn has you can type `./target/debug/unicorn --help`, or to display subcommand options `./target/debug/unicorn <SUBCOMMAND> --help`.

Currently, we have 2 main options:
### 1. Generate the BTOR2 file from the binary
```
./target/debug/unicorn beator hello.m --unroll 100 --solver boolector --out hello.btor2
```
The above command generates a BTOR2 file (i.e hello.btor2), while the unroll option specifies how many machine instructions (state transitions) Unicorn should represent in the BTOR2 file. In this example, Unicorn uses boolector to optimize at word level the number of variables the model needs. 

There are more options. For example, you can pass the option `--bitblast`, and instead the BTOR2 file will represent a logic (combinatorial) circuit.


### 2. Generate and/or test a QUBO of the binary
```
./target/debug/unicorn qubot hello.m --unroll 100 --solver boolector --out hello.unicorn --inputs 42,32;34
```
This command instead generates a QUBO model that represents 100 executed instructions, and outputs a file describing the qubo in `hello.unicorn`. If you do not use the option `--out` no output files are generated. The output files can get big very quickly.

The `--inputs` parameter is also optional. In this example, we are assuming our model consumes 2 inputs. Therefore, we are first testing our model with inputs 42 and 32, and then we perform a second test with 34 (if not enough inputs are provided, the first input is replicated to satisfy the number of inputs the model consumes). In this example, Unicorn prints one line for each test in the terminal. For our example:

```
offset:2, bad states count:0
offset:0, bad states count:1
```

This output per input means that for the first test our model does not reache ground state, therefore the inputs we provided do not reach a bad state. The second line instead, tells us that the input 32 makes 1 bad state reachable and therefore, the objective function reaches ground state.

The qubo file is divided into 5 sections, each section is separated by an empty line, and lines in each section separate values by a single space. Section are described as follows:

1. The first section consists of a single line and it contains 2 numbers: the number of variables, and the offset of the QUBO. 
2. The second section contains lines mapping input-nids of the corresponding BTOR2 file to unique identifiers of qubits. IDs of qubits are separated by commas, and the LSB comes first.
3. The third section is similar to the previous one, but instead it maps bad-state-nids to qubits ids. Bad states are booleans, therefore only one qubit-id is needed.
4. The fourth section describes linear coefficients and follows the format `<qubit-id> <linear-coeff>`.
5. The last section describes quadratic (bilinear) coefficients and follows the format `<qubit-id> <qubit-id> <quadratic-coeff>`.

Here you can see an example of how the file might look like:

```
548 1023

10000001 1,2,3,4,5,6,7,8

10000148 13
10000148 14

9 2
10 0
11 0
12 4
...

1 9 4
3 9 6
...
```

## License

Copyright (c) 2022. The Unicorn Authors. All rights reserved.

Licensed under the [MIT](LICENSE) license.

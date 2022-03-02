# Unicorn: A Compiler and Runtime System for Quantum Computing

[![Build Status](https://img.shields.io/github/workflow/status/cksystemsgroup/monster/Test)](https://github.com/cksystemsgroup/monster/actions)
[![Crate](https://img.shields.io/crates/v/monster-rs.svg)](https://crates.io/crates/monster-rs)
[![API](https://docs.rs/monster-rs/badge.svg)](https://docs.rs/monster-rs)
![Experimental Status](https://img.shields.io/badge/status-experimental-yellow.svg)
![Rust Version](https://img.shields.io/badge/Rust-v1.57.0-yellow)
![Platform](https://img.shields.io/badge/platform-linux%20%7C%20macos%20%7C%20windows-brightgreen)
[![Lines of Code](https://img.shields.io/tokei/lines/github/cksystemsgroup/monster)](https://github.com/cksystemsgroup/monster)
[![License](https://img.shields.io/crates/l/monster-rs)](https://github.com/cksystemsgroup/monster/blob/master/LICENSE)

Unicorn is a compiler and runtime system for quantum computing which translates 64-bit RISC-U binaries into precise bit-equivalent models suitable for deployment on quantum computers.

Given a RISC-U binary and a number `n` of machine instructions to execute, Unicorn builds an equivalent <b>Finite State Machine (FSM)</b> using BTOR2 formalisms, then a logic (combinatorial) circuit by replicating `n` times the FSM, and finally a <b>Quadratic Unconstrained Binary Optimization (QUBO)</b> model suitable for quantum annealers.

Given that some states of the FSM are marked as <u>bad states</u>, our models are able to determine if these states are reachable, and in such case, the concrete input(s) of the program that makes them reachable.

The number of binary variables utilized are minimized in the classical realm using SMT solvers on the word-level, and further minimized on the gate-level. Popular SMT solvers like Boolector and Z3 are supported as an optional build option.

Each step of the translation can be exported in suitable formats including BTOR2, a JSON file for QUBOs (or eventually DIMACS).

Inspired by symbolic execution, and bounded model checking, it can be used to debug classical programs. Writting a program for quantum annealers has never been so easy. Moreover, writting code to check an answer can be used to find the answer. 

Currently, we handle a <b>Turing complete</b> subset of RISC-V (i.e RISC-U), however it is future work to be able to handle full support of RISC-V, as well as outputting models suitable for gate model quantum computers.

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

First, generate a RISC-U binary. Refer to the [selfie repositorie](https://github.com/cksystemsteaching/selfie). Once selfie is installed you can generate a binary for a code you have written in a file (e.g `test.c`):

```
selfie -c hello.c -o hello.m
```

To display the available subcommands that Unicorn has you can type `./target/debug/unicorn --help`, or to display the options of the subcommands `./target/debug/unicorn <SUBCOMMAND> --help`.

Currently, we have 2 main options:
### 1. Generate the BTOR2 file from the binary
```
./target/debug/unicorn beator hello.m --unroll 100 --solver boolector --out hello.btor2
```
The above command generate a BTOR2 file (i.e hello.btor2), while the unroll option especifies how many machine instruction (state transitions) Unicorn should represent in the btor2 file. In this example, Unicorn uses boolector to optimize at word level the number of variables the models needs. 

There are more options. For example, you can pass the option `--bitblast` and instead the btor2 file will represent a logic (combinatorial) circuit.


### 2. Generate and/or test a QUBO of the binary
```
./target/debug/unicorn qubot hello.m --unroll 100 --solver boolector --out hello.unicorn --inputs 42,32;34
```
This command instead generate a qubo model that represent 100 executed instructions, and outputs a file describing the qubo in `hello.unicorn`. If you do not use the option `--out` no outputs files are generated. The output files can get big very quickly.

The option `--inputs` is also optional. In this example, we are assuming our model consumes 2 inputs. Therefore, we are first testing our model with inputs 42 and 32, and then we perform a second test with 34 (if not enough inputs are provided, the first input is replicated to satisfy the number of inputs out model consumes). In this example, 1 line for each test in the terminal. For our example:

```
offset:2, bad states count:0
offset:0, bad states count:1
```

This output per input means that for the first test our model does not reaches ground state, therefore the inputs we provided do not reach a bad state. The second line instead, tells us that the input 32 makes 1 bad state reachable and therefore, the objective function reaches ground state.

The qubo file is divided into 5 sections, each section is separated by an empty line, and lines in each section separate values by a single space. Section are described as follows:

1. The first section consists of a single line and it contains a 2 numbers: the number of variables and the offset of the QUBO. 
2. The second section contains lines mapping input-nids of the corresponding btor2 file to unique identifiers of qubits. IDs of qubits are separated by commas, and the LSB comes first.
3. The third section is similar to the previous one, but instead it maps bad-state-nids to qubits ids. Bad states are booleans, therefore only one qubit-id is needed.
4. The fourth section describes linear coefficients and follows the format `<qubit-id> <linear-coeff>`.
5. The last section describes quadratic coefficients and follows the format `<qubit-id> <qubit-id> <quadratic-coeff>`.

Here you can see an example of how the file might look like:

```
10 45

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

Copyright (c) 2020, [the Selfie authors](https://github.com/cksystemsteaching/selfie). All rights reserved.

Licensed under the [MIT](LICENSE) license.

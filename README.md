# Unicorn: A Compiler for Quantum Computers

[![Build Status](https://img.shields.io/github/workflow/status/cksystemsgroup/monster/Test)](https://github.com/cksystemsgroup/monster/actions)
[![Crate](https://img.shields.io/crates/v/monster-rs.svg)](https://crates.io/crates/monster-rs)
[![API](https://docs.rs/monster-rs/badge.svg)](https://docs.rs/monster-rs)
![Experimental Status](https://img.shields.io/badge/status-experimental-yellow.svg)
![Rust Version](https://img.shields.io/badge/Rust-v1.57.0-yellow)
![Platform](https://img.shields.io/badge/platform-linux%20%7C%20macos%20%7C%20windows-brightgreen)
[![Lines of Code](https://img.shields.io/tokei/lines/github/cksystemsgroup/monster)](https://github.com/cksystemsgroup/monster)
[![License](https://img.shields.io/crates/l/monster-rs)](https://github.com/cksystemsgroup/monster/blob/master/LICENSE)

Unicorn is a compiler for quantum computing which translates 64-bit RISC-U binaries into precise bit-equivalent models suitable for deployment on quantum computers.

Given a RISC-U binary and a number $n$ of machine instructions to execute, Unicorn builds an equivalent <b>Finite State Machine (FSM)</b> using BTOR2 formalisms, then a logic (combinatorial) circuit by replicating $n$ times the FSM, and finally a <b>Quadratic Unconstrained Binary Optimization (QUBO)</b> model suitable for quantum annealers.

Given that some states of the FSM are marked as <u>bad states</u>, our models are able to determine if these states are reachable, and in such case, the concrete input(s) of the program that makes them reachable.

The number of binary variables utilized are minimized in the classical realm using SMT solvers on the word-level, and further minimized on the gate-level. Popular SMT solvers like Boolector and Z3 are supported as an optional build option.

Each step of the translation can be exported in suitable formats including BTOR2, a JSON file for QUBOs (or eventually DIMACS).

Inspired by symbolic execution, and bounded model checking, it can be used to debug classical programs. Writting a program for quantum annealers has never been so easy. Moreover, writting code to check an answer can be used to find the answer. 

Currently, we handle a <b>Turing complete</b> subset of RISC-V (i.e RISC-U), however it is future work to be able to handle full support of RISC-V, as well as outputting models suitable for gate model quantum computers.

For more information about our work you can check our [paper](https://arxiv.org/abs/2111.12063).

### Usage

#### Binary

Once Rust is installed (see step 1 in "Toolchain Setup"), you can easily install the latest version of Monster with:
```
$ cargo install monster-rs --locked
$ monster --help
```

#### Library
Usage

Add this to your Cargo.toml:
```
[dependencies]
monster-rs = "0"
```

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
4. Install tools to build Selfie with our favorite package manager

MacOs:
```
$ brew install make gcc git
```
Linux:
```
$ apt install make gcc git
```
Windows:
```
$ choco install make -y
$ choco install mingw -y
$ choco install git -y
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

## License

Copyright (c) 2020, [the Selfie authors](https://github.com/cksystemsteaching/selfie). All rights reserved.

Licensed under the [MIT](LICENSE) license.

# monster
Monster is a symbolic execution engine for 64-bit RISC-V code

### Toolchain setup

#### Linux and Unix-like OS
1. Bootstrap rust
```
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```
2. Install Rustfmt (formatter) and Clippy (linter)
```
$ rustup component add rustfmt
$ rustup component add clippy
```
3. Add cargo to your $PATH
```
$ echo 'export PATH="$HOME/.cargo/bin:$PATH"' >> ~/.zshrc && source ~/.zshrc
```
4. Install tool for cross compilation and documentation generation
```
$ cargo install cross
$ cargo install mdbook
$ cargo install mdbook-linkcheck
$ cargo install mdbook-graphviz
```
5. install Docker and LLVM with your favorite package manager

##### MacOS
6. Install docker (needed by cross) with [this installation guide](https://docs.docker.com/docker-for-mac/install/)
```
$ brew cask install docker
```
7. Make sure you have a recent version of clang/llvm (>= v9) installed:
```
$ brew install llvm
```

##### Debian based
6. Install docker (needed by cross) with [this installation guide](https://docs.docker.com/engine/install/debian/)
7. Make sure you have a recent version of clang/llvm (>= v9) installed:
```
$ apt install llvm
```

#### Windows
We do not support Windows directly. But someone can use WSL2 to run/develop for Monster.

### Build and Test from Source
7. Test your toolchain setup by compiling monster:
```
$ cargo build --locked
```
8. Execute tests:
```
$ cargo test --locked
```


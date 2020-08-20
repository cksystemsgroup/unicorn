# monster
Monster is a symbolic execution engine for 64-bit RISC-V code

# Toolchain setup
## Install rust
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
4. Install tool for cross compilation
```
$ cargo install cross
```

## Docker and llvm
### Debian based
5. Install docker (needed by cross)
```
$ apt install docker
```
6. Make sure you have a recent version of clang/llvm (>= v9) installed:
```
$ apt install llvm
```

### Mac
5. Install docker (needed by cross) with [this installation guide](https://docs.docker.com/docker-for-mac/install/)
6. Make sure you have a recent version of clang/llvm (>= v9) installed:
```
$ brew install llvm
```

## Build and test
7. Test your toolchain setup by compiling monster:
```
$ cargo build
```
8. Execute tests:
```
$ cargo test
```

# monster
Monster is a symbolic execution engine for 64-bit RISC-V code

# toolchain setup (mac)

1. Install rust
```
$ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```
2. Install Rustfmt (formatter) and Clippy (linter)
```
$ rustup component add rustfmt
$ rustup component add clippy
```
3. Add cargo to your PATH
```
$ echo 'export PATH="$HOME/.cargo/bin:$PATH"' >> ~/.zshrc && source ~/.zshrc
```
4. Install tool for cross compilation
```
$ cargo install cross
```
5. Install docker (needed by cross) with [this installation guide](https://docs.docker.com/docker-for-mac/install/)
6. Make sure you have a recent version of clang/llvm (>= v9) installed:
```
$ brew install llvm
```
7. Test your toolchain setup by compiling monster:
```
$ cargo build
```
8. Execute tests:
```
$ cargo test
```

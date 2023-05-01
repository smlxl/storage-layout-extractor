# EVM Storage Layout Analysis

This project is a library that is able to ingest [EVM](https://ethereum.org/en/developers/docs/evm/)
[bytecode](https://ethereum.org/en/developers/docs/evm/opcodes/) and discover an approximate storage
layout for the contract described by that bytecode. It is _not_ intended to be a full decompiler,
but is instead a tool specialised for performing this discovery process.

This discovery process is performed, in broad strokes, as follows:

1. Bytecode is ingested and turned into an `OpcodeStream`.
2. This stream of instructions is executed in the `Executor` using a `VM`
   specialised for symbolic execution. It specifically looks for reads and writes to storage,
   and the operations that affect them, in terms of `Metavariable`s.
3. This `Executor` collects `ExecutionTrace`s that provide some kind of evidence (in the form of
   a heuristic-based `ImplicationSet`) toward the type of the storage variable.
4. These `ExecutionTrace`s and their corresponding `ImplicationSet`s are then combined by the
   `Unifier`. It does this by performing a kind of usage-based type inference that refines the
   type of the storage variable based on the available evidence.
5. From there, it can then output its best-effort storage layout analysis.

## Development

This repository is written in [Rust](https://www.rust-lang.org), a high-performance and
low-level language with a smart compiler that helps to write reliable and fast software. If you
haven't worked with Rust before, take a look at the ["New to Rust?"](#new-to-rust) section below!

### Setting Up

Getting set up with this project is pretty simple.

1. Clone the repository. If you don't want to contribute directly you can use HTTPS clones:

   ```shell
   git clone https://github.com/smlxlio/storage-layout-analyzer.git
   ```

   If you _do_ want to contribute, we recommend cloning over SSH:

   ```shell
   git clone git@github.com:smlxlio/storage-layout-analyzer.git
   ```

2. Building the project is then as simple as entering the project directory and using `cargo`.

   ```shell
   cargo build
   ```

3. You can also test using `cargo`.

   ```shell
   cargo test
   ```
   
For contributions this repository works on a 
[Pull Request](https://github.com/smlxlio/storage-layout-analyzer/pulls) and subsequent review 
model, supported by CI.

### New to Rust?

If you are new to working with Rust, a great place to start is the official
[Rust Book](https://doc.rust-lang.org/book/). It gives a great overview of the language and
general style. It's also worth getting familiar with the following tools:

- [Rustup](https://rustup.rs), the Rust toolchain installer.
- [Cargo](https://doc.rust-lang.org/cargo/), the Rust build tool and package manager.
- [docs.rs](https://docs.rs), a site providing up-to-date crate (package) documentation for all
  packages published to [crates.io](https://crates.io), the official package registry.
- [Rustdoc](https://doc.rust-lang.org/rustdoc/index.html), the ecosystem's official 
  documentation tool.

In terms of development tooling, there are two major options in this space.

- [IntelliJ Rust](https://intellij-rust.github.io) is an open source plugin for the semi-open
  source [IntelliJ](https://www.jetbrains.com/idea/) IDE. It can also run in
  [Clion](https://www.jetbrains.com/idea/) where it provides a slightly better experience.
- [Rust Analyzer](https://rust-analyzer.github.io) is the official implementation of the
  [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) for Rust,
  and will work with any LSP compatible host.

# Contributing

This document exists as a brief introduction to how you can contribute to the storage layout
extractor project. It includes a guide to [getting started](#setting-up-for-development) and
[contributing to `main`](#getting-your-work-on-main), as well as a [code tour](#code-tour) that
briefly goes over the major components of the library.

This repository is written in [Rust](https://www.rust-lang.org), a high-performance and
low-level language with a smart compiler that helps to write reliable and fast software. If you
haven't worked with Rust before, take a look at the ["New to Rust?"](#new-to-rust) section below!

## Setting Up for Development

Getting set up with this project is pretty simple.

1. Clone the repository. If you don't want to contribute directly you can use HTTPS clones:

   ```shell
   git clone https://github.com/smlxlio/storage-layout-extractor
   ```

   If you _do_ want to contribute directly to the tree, we recommend cloning over SSH:

   ```shell
   git clone git@github.com:smlxlio/storage-layout-extractor.git
   ```

2. Building the project is then as simple as entering the project directory and using `cargo`.

   ```shell
   cargo build
   ```

3. You can also test using `cargo`.

   ```shell
   cargo test
   ```

## Getting Your Work on `main`

For contributions this repository works on a
[Pull Request](https://github.com/smlxl/storage-layout-extractor/pulls) and subsequent review
model, supported by CI to check that things avoid being broken. The process works as follows:

1. If necessary, you fork the repository, but if you have access please create a branch.
2. You make your changes on that branch.
3. Pull-request that branch against `main`.
4. The pull request will be reviewed, and CI will run on it.
5. Once reviewers accept the code, and CI has passed, it will be merged to main!

## Code Tour

The code in this repository is primarily structured around each of the phases described in
the [readme](../README.md).

- `data`: This contains useful data structures necessary for the implementation of the library.
- `disassembly`: This contains the implementation of
  the [disassembler](../src/disassembly/disassembler.rs) and
  the [instruction stream](../src/disassembly/mod.rs) used during execution.
- `error`: This contains the strongly-typed [error representation](../src/error/mod.rs) for the
  library. The library uses a unified error representation at its interface, but also has individual
  error representations for each "phase" of the analysis. This portion of the library also
  implements conversions between the various error types, and mechanisms for locating errors in
  bytecode.
- `extractor`: This contains the [driver](../src/extractor/extractor) for the library itself, as well
  as the implementation of the analysis state machine that makes it harder to get into broken states
  while analysing a [contract](../src/extractor/contract.rs).
- `inference`: This contains the [type checker](../src/tc/mod.rs), as well as the
  [type language](../src/tc/expression.rs) used by the library. It also contains the
  [lifting passes](../src/tc/lift/mod.rs) and the [inference rules](../src/tc/rule/mod.rs) used by
  the inference process, and the implementation of the [unifier](../src/tc/unification.rs).
- `opcode`: This contains the [opcode definition](../src/opcode/mod.rs), and the implementations of
  each individual EVM opcode and their symbolic semantics.
- `vm`: This contains the implementation of the symbolic [virtual machine](../src/vm/mod.rs) and
  the [state](../src/vm/state/mod.rs) it needs to execute.

This project is a _library_ and hence does not come with a driver to enable its use directly as a
product. It can easily be wrapped in a CLI or server to enable working with it in a more user-facing
fashion.

A good demonstration of how to use the library in both simple and complex scenarios can be found in
the [integration tests](../tests). Reading the common [test utilities](../tests/common/mod.rs) will
likely be a good introduction to the various modes of usage, as well as an explanation of the kind
of functionality a driver program will require.

## New to Rust?

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

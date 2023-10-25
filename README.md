<p align=center>
  <img src="https://avatars.githubusercontent.com/u/90545451?s=200&v=4"/>
</p>

# EVM Storage Layout Extractor

This project is a library that is able to ingest [EVM](https://ethereum.org/en/developers/docs/evm/)
[bytecode](https://ethereum.org/en/developers/docs/evm/opcodes/) and discover an approximate storage
layout for the contract described by that bytecode. It is _not_ intended to be a full decompiler,
but is instead a tool **highly** specialised for performing this discovery process. 

See our [announcement](https://blog.smlxl.io/announcing-bytecode-generated-storage-layouts-on-evm-storage-96761758d397) for more details
or check the [deepdive post on our blog.](https://blog.smlxl.io/a-deep-dive-into-our-storage-layout-extractor-51554185d8af)

This discovery process is performed, in broad strokes, as follows:

1. Bytecode is ingested and disassembled into an instruction stream that is amenable to analysis.
   This is a sequence of Opcodes that is equivalent to the bytecode.
2. The stream of instructions is executed symbolically on a specialised EVM implementation. This
   execution is both **speculative** and **total**, exploring all possible code paths that can
   influence the type attributed to a given storage location.
3. For each value seen in the program during execution, the VM builds a **symbolic value** (a little
   tree structure) that represents the operations performed to that particular piece of "data".
4. These execution trees are passed to a type inference process. This process starts by _lifting_,
   which turns low-level constructs into more-general high-level ones. The results of this are then
   fed to _inference rules_ that output **type inference judgements** about the trees they analyse.
   Finally, these inferences are combined with a _unifier_ to perform whole-program type inference.
5. The resolved types associated with each storage slot are then turned into a **storage layout**
   that describes the type of each storage slot that was encountered.

For more information on the process with specific reference to concrete pieces of code, see the
documentation in [`lib.rs`](src/lib.rs). This also provides a basic usage example for the library,
though more complex ones can be found in the [tests](tests).

## Extending the Library

The primary means of extending this library to get better layouts is by extending the type inference
engine. This is done by either writing new **lifting passes** or **inference rules**, and you can
find more information on this process in the documentation
on [extending the library](./docs/Extending%20the%20Library.md).

## Contributing

If you want to contribute code or documentation (non-code contributions are _always_ welcome) to
this project, please take a look at our [contributing](./docs/CONTRIBUTING.md) documentation. It
provides an overview of how to get up and running, as well as what the contribution process looks
like for the library. 
We are also available on our [Telegram group](https://t.me/+zw0fuNoYg39hZWRh) if you have any questions.

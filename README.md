# MLIR Semantics in Lean

This project provides Lean semantics and syntax for `MLIR`'s `LLVM` dialect and tactics to make proofs easier.

It's modelling of `MLIR` is based on https://github.com/opencompl/lean-mlir but does not share any code with it anymore.

## Quick Start

1. Compile your code to MLIR or use the [extractor](./extractor) to generate MLIR from a `compile_commands.json` or LLVM IR.
2. Use the [extractor](./extractor) to generate the Lean Files.
3. State and prove the behavior of your functions. See [examples](./examples) for an introduction to the most important concepts and tactics. We recommend the order of the functions in [`source.c`](./examples/source.c). A more exhaustive but difficult to read explanation of the tactics is located in [.agents/skills](./.agents/skills).
# extractor

Turns a C project into Lean definitions over the `MLIR` framework: one `.lean`
file per function or constant global, defined with `mlir_def` /
`mlir_const_def`.

This tool provides three commands:

```
compile_commands.json ──compile──▶ module.ll ──translate──▶ module.mlir ──import──▶ *.lean
```

`compile` is designed for a `compile_commands.json` of a C compile run. If you have another LLVM-based frontend compiler, you'll have to find out yourself how to generate the single LLVM IR module file.

## Building

The `import` stage links MLIR through [melior](https://github.com/mlir-rs/melior),
which needs an LLVM 23 install with MLIR. Point the `mlir-sys` build at it:

```sh
export MLIR_SYS_230_PREFIX=/path/to/llvm-23
export TABLEGEN_230_PREFIX=/path/to/llvm-23
cargo build --release
```

`.cargo/config.toml` sets both for one local install; override them for yours.

## LLVM tools

`compile` and `translate` run `clang`, `llvm-link`, `mlir-translate` and
`mlir-opt`. They come from `PATH`, or from `--llvm-bin <dir>` (env `LLVM_BIN`).
All four should be from the same LLVM release.

## Usage

### `compile <compile_commands.json> <out>`

Rebuilds every C source of a compilation database as textual LLVM IR and links
the result into `<out>/module.ll`.

- Each command's `-c` and `-o x.o` become `-S -emit-llvm -o <out>/x.ll`; all
  other flags are kept.
- Assembly sources (`.S`) are skipped.
- Every command must invoke the same `clang` the extractor resolves; a
  database built with another compiler is rejected.

### `translate <module.ll> <out>`

Imports the IR into the MLIR `llvm` dialect and canonicalizes it, writing
`<out>/module.mlir` in generic form:

```sh
mlir-translate --import-llvm module.ll \
  | mlir-opt --canonicalize=region-simplify=disabled --mlir-print-op-generic
```

### `import <module.mlir> <root> <target> <target_module> [mappings.json] --root-func <name>...`

Writes Lean files for every `llvm.func` and `llvm.mlir.global`
reachable from the `--root-func` symbols, following `llvm.call` callees and
`llvm.mlir.addressof` globals.

| Argument | Meaning |
| --- | --- |
| `root` | Root of the Lean project. |
| `target` | Default directory for the files, relative to `root`, e.g. `Firedancer/Ref/Mlir`. |
| `target_module` | Default namespace, e.g. `Firedancer.Ref.Mlir`. |
| `mappings.json` | Optional per-symbol overrides of `target` and `target_module`. |
| `--root-func` | Entry symbol; repeatable. |
| `--stub` | Symbol regex stubbed by hand; repeatable. |

Symbol `f` lands in `<root>/<target>/f.lean` as `<target_module>.f`; a `.` in a
symbol (a static local, `f.K`) becomes `_` in its Lean name, file and import, and
the `@f.K` binding keeps the symbol. Its dependencies are imported as
`<target with / as .>.<g>` and bound in the `with` clause, so `target` and
`target_module` must name the same module path.

A stub (a `--stub` match, or a declaration without a body) is neither written
nor followed: its callers import and bind it at its mapped path, where a
hand-written module defines it, e.g. a `Func` of axioms. A function reaching a
stub is a `noncomputable mlir_def`. Every global is imported, mutable ones too.

Mappings are tried in order; the first whose regex matches the whole symbol
wins, and the command-line target is the fallback:

```json
[
  ["fd_sha512_.*", "Firedancer/Sha512/Mlir", "Firedancer.Sha512.Mlir"]
]
```

A generated file looks like:

```lean
module

public import MLIR.Semantics.Func
public import MLIR.Syntax.Elab

public import Firedancer.Ref.Mlir.callee

namespace Firedancer.Ref.Mlir

@[expose] public section

mlir_def f := "llvm.func"() <{...}> ({ ... }) : () -> ()
    with
      @callee := Firedancer.Ref.Mlir.callee

end

end Firedancer.Ref.Mlir
```

Existing files are overwritten.

## Example

```sh
extractor --llvm-bin ~/.local/llvm-23/bin compile build/compile_commands.json out
extractor --llvm-bin ~/.local/llvm-23/bin translate out/module.ll out
extractor import out/module.mlir ~/lean-mlir Firedancer/Ref/Mlir Firedancer.Ref.Mlir \
  mappings.json --root-func fd_ed25519_verify
```

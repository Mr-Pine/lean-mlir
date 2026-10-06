# Pinned Agave Ed25519 compiler artifacts

These artifacts come from `solana-ed25519 0.2.4`, the exact registry package
selected by Agave commit `e818d643945cd82c7144013af58ccf82d31df2dd`.
The cached `.crate` archive SHA-256 was checked against Agave's `Cargo.lock`:
`ff4c7caf3fe3d70815869a5838ee45b4d2b009eaacea1790ef3cd9b3c89edbbd`.
All 93 archived files were compared byte-for-byte with the copied source.
`source-manifest.json` records their hashes and registry VCS metadata.

`source/` is the unmodified archived crate. The extraction copies it and appends
`wrappers.rs` to `src/lib.rs`, `reduce64_wrapper.rs` to the AVX2 field module,
and `point_wrappers.rs` to the AVX2 Edwards module. Placing the latter wrappers
in their owning modules allows observing private helpers and representations
without changing their visibility or arithmetic bodies.

`Cargo.extract.toml` retains the exact enabled dependency versions from Agave's
lock file and enables `alloc,precomputed-tables,zeroize,rand_core,digest`.
It removes disabled optional dependencies and development dependencies because
resolving the complete standalone published manifest requires an uncached
`ff_derive` dependency even though that dependency is not compiled. The full
original manifests remain in `source/`. The extraction profile uses optimization
level 3, one codegen unit, disabled overflow/debug checks, and `panic=abort`.
This is a dedicated extraction build, not a byte-identical Agave release binary.

## Reproduction

```bash
python3 SSA/Projects/Agave/Ed25519/MLIR/extract.py \
  --out /tmp/ed25519-extract \
  --llvm-bin /path/to/llvm-22/bin \
  --llvm-lib /path/to/llvm-22/libraries
```

Rust is pinned to `1.98.1`, whose backend is LLVM `22.1.8`. The checked artifacts
were imported with Ubuntu LLVM/MLIR `22.1.2`. The optional `--llvm-lib` argument
is needed only when using unpacked shared libraries outside the loader's paths.
`generated/manifest.json` records compiler versions, every exact command, input
hashes, original symbols, and artifact hashes. `verify.py` checks those hashes.

`llvm-extract --keep-const-init` retains referenced constant table initializers.
LLVM internalization and global dead-code elimination remove unrelated constant
definitions retained by that option, preserving the selected function body.
Simple forwarding wrappers are resolved to their original function bodies;
the manifest records the wrapper and selected original symbol separately.
Pure output observations that retain calls are extracted recursively and run
through LLVM's `internalize,inline,function(sroa,instcombine,simplifycfg),globaldce`
pipeline with inlining threshold 100000. Their `.before-inline.ll` artifacts
are retained. No Python code rewrites instructions or synthesizes arithmetic IR.

## Kernel boundaries

The field artifacts include serial multiply/square and AVX2 multiply,
square-and-negate-D, reduce, reduce64, new, and split. Pure observations cover
all five packed output registers of AVX2 multiplication, squaring, reduce,
and reduce64, and all five output limbs of serial multiplication.

AVX2 point observations cover all five output registers of doubling and
cached addition/subtraction. They take the original raw packed point coordinates
by value. The pure signatures use Rust's `__m256i` C ABI, imported as
`vector<4xi64>`; bitcasts expose the implementation's packed `vector<8xi32>`
layout. Representation validity and limb bounds remain proof obligations.

Additional artifacts expose serial point doubling, projective/affine cached
addition/subtraction, point compression, width-5/width-8 NAF conversion,
double-base multiplication in both backends, and the strict verifier wrapper.
These retain memory effects and/or calls. Their presence is not a completed
whole-verifier proof and does not supply semantics for external callees.

Encoding observations cover all five limbs of serial `from_bytes`, all four
little-endian output words of serial `to_bytes`, and all twenty serial limbs
returned by AVX2 `split` (projection number `5 * coordinate + limb`). All
`to_bytes` and `split` observations are pure. The middle three `from_bytes`
observations retain a sixteen-byte stack slot, two input-word stores, one
unaligned word load, and lifetime markers. This exact compiler lowering is
retained; their proof must account for that small memory frame.

## Import compatibility

The pure field and AVX2 point observations consist of integer/vector arithmetic,
constant shuffles, lane insertion/extraction, casts, and returns. They require
RIR's vector casts and lane-wise multiplication semantics. LLVM 22 prints
`overflowFlags` as integer masks; bit 0 is `nsw` and bit 1 is `nuw`, and both
must be preserved. Partially poison vector constants are imported into explicit
`undef`/`poison` plus lane-insertion sequences.

The full memory-based reduce/reduce64/new functions include
`llvm.intr.experimental.noalias.scope.decl` metadata declarations. Double-base
multiplication and NAF additionally require dynamic GEPs, `llvm.intr.scmp`,
unreachable/panic handling, global addresses and constant lookup tables, and
proofs for called functions. Compression additionally calls field inversion
and arithmetic helpers. Per-kernel operation counts are in the manifest;
the framework extensions and actual execution proofs are maintained separately.
`compatibility.json` compares selected executable bodies against the upstream
`new-semantics` translator at `2c71edf3d`; it excludes global-initializer operations
and distinguishes literal SSA GEP indices from genuinely dynamic indices.

The trusted boundary includes Rust and LLVM compilation/optimization, MLIR
import, and RIR's syntax translation. The generated artifacts establish which
code a proof concerns; they do not prove the compiler itself correct.

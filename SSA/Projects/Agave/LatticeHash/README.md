# Agave lattice-hash conformance proof

This directory contains a kernel-checked equivalence proof for the manually
transcribed semantics of Agave's width-one reference path, eight-lane AVX2
path, and sixteen-lane AVX-512 path. For every finite legal public event
sequence in the model, all three paths produce the same complete sequence of
returned 1024-element `LtHash` values.

The model is pinned to Agave commit
`e818d643945cd82c7144013af58ccf82d31df2dd`:

| Source | SHA-256 |
|---|---|
| `lattice-hash/src/batch/arch.rs` | `6cef9f4897406efa5dfea7b3f16b799b0f71fb398cc017595351085ac4dc1ca0` |
| `lattice-hash/src/batch.rs` | `fdccfacf2d2475f129a9326188d688b4db0cc2a8f156cf65c87cde44becd1394` |
| `lattice-hash/src/lt_hash.rs` | `2a2723d0ea4d6130b22ae76a6a5b677e95eabe4dd7062d756c137fd9d22d6a7a` |
| `Cargo.lock` | `1230c33b5344dc38474a99c388e0343869e4e174485f544818db8303e0205990` |
| `blake3-1.8.7/src/portable.rs` | `85ed8cd8f601e6801c0a26358c7ac70e29759445cfe39c584f40af072a201601` |
| `blake3-1.8.7/src/lib.rs` | `a187904c4b12ea7c100557c0f167cc91a034e391ddeb56c9db65f7d400a4b566` |
| `blake3-1.8.7/src/platform.rs` | `954e3564bb976c333cfaa68fc672a8543afc2e021c8b89e8d9393816b0ad90d1` |

The proof repository revision on which this development was based is
`b1c63110b105c53a593efee2f07a3e14f379a581`.

## Main result

`AgaveBlake3Reference.every_legal_portable_trace` is the strongest
source-shaped theorem. Its only premise is that the small public API
interpreter accepts a chronological event sequence. It constructs retained
memory executions for the reference, AVX2, and AVX-512 widths, each with
exactly the complete output log computed from an independently structured
portable short-message BLAKE3 reference and the common long-message fallback.
Thus every `take_lt_hash` result agrees, including repeated drains and reuse.

`AgaveOutputLog.reference_eq_avx2_eq_avx512` is the direct three-way
conformance theorem for actual executions of the same event sequence. It
concludes

```text
reference output log = AVX2 output log = AVX-512 output log
```

A legal sequence may contain arbitrary message-part boundaries, empty
messages, messages that spill past 1024 bytes, normal `finish` and `Drop`,
whole-message insertion, full and partial flushes, precomputed `mix_in`
effects, repeated `take_lt_hash`, and accumulator reuse. `every_legal_trace`
proves that every sequence accepted by the interpreter has retained-memory
executions at all three widths, so the concrete trace relation does not
silently remove any of these cases. Full-log equality synchronizes the public
event sequence. `AgavePhysicalMixed.physical_reference_eq_avx2_eq_avx512`
additionally proves equality of an idle observation when the paths reach the
same semantic state through different fragmentation or flushing histories.

The result derives all buffer, padding, bounds, transpose, mask, compression,
and reduction facts. Callers do not assume a correct SIMD backend or valid
staging memory. The physical model uses a retained `16 × 1024` byte
allocation. It permits arbitrary stale suffixes and proves that append, final
block zeroing, spill, drop, clear, tail hashing, and lane reuse expose exactly
the live bytes that the source uses.

Messages of at most 1024 bytes use a fully defined BLAKE3 compression and
2048-byte root XOF model. `portableLtHash_eq_oneChunk` independently
transcribes the locked portable source's sequential assignments, seven rounds,
chunk update loop, withheld final block, flags, XOF loop, serialization, and
little-endian `u16` decoding, then proves equality of all 1024 outputs. The
proof derives termination for every length at most 1024; it has no fuel or
default-value premise. `publicHash_eq_portableReference` connects that program
to the scalar hash used by the lifecycle proof.

Longer messages use an arbitrary common `longHash` function. No BLAKE3
correctness or collision assumption about that function is needed for the
three-way equivalence theorem.

`AgaveSerialStreaming.reference_eq_avx2_eq_avx512` requires stronger trace
synchronization but weaker hasher assumptions for long messages: when the
public `add_part` trace is identical, equality holds for arbitrary hasher
state, update, and finalize functions, even when the three paths begin with
unrelated dirty serial states.
It assumes no update associativity, empty-update identity, partition
independence, or BLAKE3 correctness. Comparing equal long byte strings supplied
with different part boundaries uses the ordinary BLAKE3 streaming contract,
as represented by `longHash`.

## Proof layers

- `Primitives.lean` proves the AVX2 shift/or rotations, AVX2 blend masks,
  AVX-512 opmask construction, lane control arithmetic, and packed wrapping
  `u16` addition.
- `Compression.lean` defines the exact IV, seven BLAKE3 rounds and schedules,
  state initialization, feed-forward, and root XOF, then proves projection of
  vector compression onto every lane.
- `BatchControl.lean` proves the masked variable-length loop, block flags,
  sizes, counters, termination, read bounds, and root descriptor for every
  mixture of lengths 0 through 1024.
- `Transpose.lean` symbolically executes the exact 8×8 and 16×16 intrinsic
  transpose networks.
- `TransposeReduction.lean` proves input loading, output transpose, complete
  output coverage, and wrapping-`u16` accumulation into an arbitrary existing
  accumulator.
- `Staging.lean` proves the message-level builder, flush, drain, and reuse
  invariant.
- `Equivalence.lean` composes the concrete compression, control, transpose,
  reduction, and lifecycle results and constructs proved backend instances.
- `Blake3Reference.lean` independently models the locked portable BLAKE3
  one-chunk path and proves it equal to the scalar short-message model.
- `PhysicalStaging.lean` refines the logical staging model to retained finite
  byte storage, including stale data, zero padding, spills, scalar tails, and
  direct full-batch kernel reads.
- `MixedLifecycle.lean` adds arbitrary precomputed accumulator effects.
- `PhysicalMixed.lean` composes retained storage and mixing into the main
  end-to-end result and proves that every abstract legal trace can be lifted.
- `OutputLog.lean` records every actual drain result, proves the whole log
  equal at all three widths, and constructs executions for every legal event
  sequence.
- `Conformance.lean` composes the portable BLAKE3 refinement with the complete
  public output-log theorem.
- `SerialStreaming.lean` proves identical spill/update call traces agree for
  an otherwise arbitrary deterministic streaming hasher.
- `ExecutableCompression.lean` provides materialized BLAKE3 evaluators and
  proves their equality with the scalar model, without running fixture tests.
- `Validation.lean` checks 11 independent single-block fixtures and seven
  multi-block fixtures of 2048 output bytes each, covering XOF counters 0–31.
  `Tests.lean` is the test entry point; the core aggregator excludes these
  fixtures.
- `AxiomAudit.lean` guards the expected axiom dependencies at the exported
  theorem boundaries in one place.
- `Forgotten.lean` and `ForgottenOutput.lean` formalize the necessary
  lifecycle boundary and its concrete unequal outputs.

## Necessary lifecycle boundary

An unrestricted safe-Rust API equivalence statement is false. After committing
one-byte messages `A` through `I`, a caller can use
`core::mem::forget` on an unfinished builder containing `Z`, drain the
accumulator, add `C`, and drain again. The width-one, AVX2, and AVX-512 paths
then hash `ZC`, `IC`, and `AC`, respectively.

`AgaveForgotten.final_outputs_pairwise_different` proves the resulting
LtHashes are pairwise unequal in the concrete BLAKE3 model: their first `u16`
values are 27344, 5968, and 47808. The proof uses no injectivity or
collision-resistance assumption. Debug builds reject the dirty drain with the
source assertion; release builds exhibit the divergence. The main theorem
therefore models ordinary builder completion or drop and deliberately has no
constructor for leaking a builder.

## Trust boundary

Lean checks the mathematical refinements from the transcribed source semantics.
The remaining external trust is:

- faithful transcription of the pinned Rust, locked BLAKE3 source, and x86
  intrinsic operations, including identification of the relevant short-input
  BLAKE3 path;
- Rust/LLVM lowering, pointer and alignment behavior, x86 little-endian
  instruction semantics, ABI, and runtime feature dispatch;
- equivalence of any upstream BLAKE3 CPU backends used by the scalar fallback;
- Lean's kernel and its standard logical axioms.

The guarded axiom audits for the final theorems report only `propext`,
`Classical.choice`, and `Quot.sound`. The development contains no custom
axioms, `sorry`, `admit`, `native_decide`, or disabled kernel checking.
It is a source-model proof, not a Rust extraction, LLVM refinement, or
machine-code verification result.

## Checking

```sh
lake build SSA.Projects.Agave.LatticeHash
lake build SSA.Projects.Agave.LatticeHash.Tests
lake env lean SSA/Projects/Agave/LatticeHash/Conformance.lean
lake env lean SSA/Projects/Agave/LatticeHash/AxiomAudit.lean
lake env lean SSA/Projects/Agave/LatticeHash/Blake3Reference.lean
lake env lean SSA/Projects/Agave/LatticeHash/OutputLog.lean
lake env lean SSA/Projects/Agave/LatticeHash/PhysicalMixed.lean
lake env lean SSA/Projects/Agave/LatticeHash/ForgottenOutput.lean
lake -R build
```

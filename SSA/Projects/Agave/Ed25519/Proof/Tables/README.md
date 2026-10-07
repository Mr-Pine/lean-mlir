# Odd-multiple table refinement

`Dynamic.lean` follows the two width-5 constructors: entry zero is the input
point, and each successive entry adds its double. It proves that serial and
AVX2 entries are related by a nonzero common projective scale. Using the
Firedancer Edwards group development, it also proves that entry `k` represents
`(2*k+1) • A`.

`Static.lean` decodes the complete immutable initializers from the extracted
serial and AVX2 double-base MLIR files. The serial table is 7,680 bytes (64
affine Niels records); the AVX2 table is 10,240 bytes (64 cached SIMD records).
Kernel-checked certificates establish:

- every decoded record equals the cache of its stated extended point;
- corresponding serial and AVX2 points have a nonzero common scale;
- entry zero is the RFC base point;
- every next serial point is the normalized sum of the preceding point and
  twice the base point.

These imply that every static entry represents the same advertised odd
multiple. `doubleBase_schedule_related` combines the dynamic and static tables
without assuming table correctness.

Regenerate with `python3 SSA/Projects/Agave/Ed25519/Proof/Tables/generate.py`;
add `--check` for a read-only reproducibility check. The generator is not trusted
for arithmetic: the emitted finite certificates use `decide +kernel`.

`SerialConstructor.lean` and `Avx2Constructor.lean` retain the exact pinned
constructor bodies. `ConstructorGlobals.lean` imports the serial constructor's
40-byte `2d` initializer, and `ConstructorConstant.lean` derives its five limb
reads, bounds and curve-field value from the initializer's presence in memory.
`ConstructorMemory.lean` proves the seven successor-record address bounds and
the exact final 1,280-byte copy in both constructors. It does not yet execute
the constructor loops or establish their output point multiples. `Audit.lean`
checks the axiom dependencies of these boundaries and the static certificates.
Reproduce the exact constructor bodies and constant with
`python3 SSA/Projects/Agave/Ed25519/Proof/Tables/import_constructors.py --check`
and `python3 SSA/Projects/Agave/Ed25519/Proof/Tables/import_constructor_globals.py --check`.

This layer proves mathematical constructors and byte-table contents. It does
not by itself prove that a RIR execution performs the dynamic constructor,
loads the intended immutable allocation, preserves the global bytes, or uses
the same signed-digit schedule. Those are separate memory/control-flow
refinement obligations. The `ByteGlobal` descriptors retain the exact symbols,
lengths, initializer bytes and alignments needed for those obligations.

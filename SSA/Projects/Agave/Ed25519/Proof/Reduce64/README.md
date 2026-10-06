# AVX2 reduce64 proof boundary

`Arithmetic.lean` proves the exact two-chain integer reduction preserves the
field residue. This algebraic theorem has no input bound. Under the simple
per-column bound `z[i] < 2^63`, it also proves all 64-bit additions are exact
and every output fits the shared loose 26/25-bit invariant and a u32 lane.

`Words.lean` proves the wrapping BitVec64 calculation equals that integer
schedule under the same bound. `ScalarSafety.lean` discharges all emitted
`nsw`/`nuw` arithmetic checks, using kernel-checked arithmetic and no native
or bitblasting axiom. These safety lemmas hold even for arbitrary u64 inputs;
residue preservation still needs the column bound.

`Program.lean` and `Observe0.lean` through `Observe4.lean` contain verbatim
compiler-generated MLIR regions imported into RIR. The extraction files and
compiler provenance are under `../../MLIR/`.

**Remaining obligation:** no theorem here yet connects execution of these RIR
programs (including vector lane packing and memory effects) to `Word.reduce`.
The imported programs and the proven word model are distinct artifacts until
that bridge is supplied. This directory is not a complete reduce64 RIR
correctness proof, nor a complete Ed25519 verification proof.

`Audit.lean` guards the standard-three-axiom inventories of the residue,
output-bounds, word-refinement, and scalar poison-flag endpoints.

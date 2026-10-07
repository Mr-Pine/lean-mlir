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

`Execution/Kernel.lean` connects actual execution of the standalone reduction
program, including vector lane packing and memory effects, to `Word.reduce`.
`Execution/Readback.lean` proves the stored integer limbs and field residues
under the column bound. The wrapping execution theorem requires only valid
caller memory ranges and a well-formed global state. These endpoints passed
direct Lean validation through `Execution/Audit.lean` on 2026-10-07.

The proof boundary remains the extracted RIR program. LLVM alias metadata,
physical alignment, and the source-to-RIR validity contract remain separate
obligations; this is not a complete Ed25519 verification proof.

`Audit.lean` guards the standard-three-axiom inventories of the residue,
output-bounds, word-refinement, and scalar poison-flag endpoints.

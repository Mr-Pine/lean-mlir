# AVX2 reduction: verified components and remaining work

`ReduceProgram.lean` embeds the LLVM22-imported basic blocks of the five
`agave_avx2_field_reduce_observe_N` wrappers. Each wrapper accepts five 256-bit
registers, constructs the actual pinned `FieldElement2625x4`, calls its original
`reduce` method, and returns one selected output register. The compiler inlines
that method. These functions have no memory operations, external calls, or loops.
`check_reduce_program.py` verifies that every embedded block matches generated
MLIR exactly, including numeric NSW/NUW attributes.

Checked mathematical results in `ReduceArithmetic.lean`:

* Input integer = reduced integer + topCarry*(2^255 - 19), for arbitrary
  natural-number coefficients.
* Each field residue modulo `2^255 - 19` is preserved.
* For unrestricted u32 limbs, even limb 0 is at most `2^26 - 1 + 19*127`,
  other even limbs at most `2^26 - 1 + 127`, and odd limbs at most
  `2^25 - 1 + 63`.

`ReduceBitcast.lean` supplies checked RIR vector bitcast lemmas and the exact
32/64-bit lane packing identities. These lemmas were validated in the original
support module before extraction into this focused module. `ReduceAudit.lean`
records their standard-axiom inventories.

The end-to-end RIR execution theorem is **not complete**. In particular, these
components do not yet connect the imported observers' arithmetic instructions
to the natural-number carry specification. NSW/NUW safety and vector operation
normalization remain to be integrated using kernel-checked arithmetic proofs.
A preliminary `bv_decide` approach was excluded because this Lean nightly
introduced native decision axioms.

The source observers also do not establish a Lean memory refinement for the
pointer ABI wrapper. Such a theorem must additionally prove that the wrapper
stores the five observed registers in its output allocation.

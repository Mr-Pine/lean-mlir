import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressMath
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressSqrtAudit
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Audit

/-!
Decompression proof boundary, pinned to registry `solana-ed25519` 0.2.4,
archive SHA256 `ff4c7caf3fe3d70815869a5838ee45b4d2b009eaacea1790ef3cd9b3c89edbbd`.

Proved here:
* the concrete D/SQRT_M1 limb constants;
* the `pow22501` and `pow_p58` addition-chain exponents;
* both comparisons used for successful square-root selection, the extra
  nonsquare-root correction comparison, and even-root normalization;
* success iff a root exists, with no assumptions on u or v;
* for every 256-bit input, decoding returns P iff `Bridge.Encodes bytes P`;
* exact rejection, canonical round-trip, field-equal y aliases, both sign
  bits at x=0, and acceptance of low-order points by decompression itself.

Execution progress is audited separately in `DecompressExecution.Audit`.
The supplementary `decompress-manifest.json` pins seven original helper bodies
from the identical full-crate LLVM artifact. Exact RIR imports now cover the
decoder, sqrt_ratio_i, pow22501, pow2k, to_bytes, subtle byte equality, and
black_box; `DecompressExecution.linkedProgram` closes every call using those
bodies and the existing serial multiplication kernel. `step_1`, `step_2`, and
`pow_p58` occur inlined in the extracted decoder/square-root bodies.

Still missing from the complete Agave RIR execution proof:
1. The pow2k loop needs an iteration/termination invariant and output bounds;
   pow22501 needs all its stack objects and calls composed through the chain.
2. Field ct_eq uses actual canonical serialization and subtle's byte equality.
   Their complete pointer-based executions still need to be related to the
   already proved to-bytes arithmetic/observation contracts.
3. sqrt_ratio_i needs a complete instruction/state proof connecting all field
   operations, three comparisons, correction masks, and final parity choice.
4. Decompression's entry and success blocks need state composition, including
   scratch lifetimes, copy/frame preservation, and final X/Y/Z/T payload stores.
   The shared Option-tag return block alone is proved to execute exactly.
5. The actual black_box alloca/store/load/return sequence is proved in RIR's
   sequential memory-value semantics. The preserved volatile_ attribute does
   not add a trace event; concurrent/volatile event behavior, alignment, and
   LLVM noalias promises require a separate LLVM-to-RIR correspondence argument.

No cryptographic helper remains an unresolved external call in the linked
program. The outstanding whole-program refinement is not supplied as a hidden
primitive contract or as an assumed equality theorem.

`refinement_of_eq` makes the missing decoder-execution equality an explicit
premise. None of the unconditional mathematical theorems supplies it or
substitutes an abstract operation for imported machine code. The guarded
audit below fails compilation for every axiom outside `propext`,
`Classical.choice`, and `Quot.sound`; it permits the smaller closures of
elementary results.
-/

/-- info: All 9 decompression encoding endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Encoding.Decompress.fromBytesWord_field,
    ``Agave.Ed25519.Encoding.Decompress.step2_encodes,
    ``Agave.Ed25519.Encoding.Decompress.decompress_eq_some_iff,
    ``Agave.Ed25519.Encoding.Decompress.decompress_eq_none_iff_nonsquare,
    ``Agave.Ed25519.Encoding.Decompress.decompress_eq_none_iff,
    ``Agave.Ed25519.Encoding.Decompress.decompress_compress,
    ``Agave.Ed25519.Encoding.Decompress.decompress_congr,
    ``Agave.Ed25519.Encoding.Decompress.decompress_zero_x,
    ``Agave.Ed25519.Encoding.Decompress.decompress_small_order_iff]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All 9 decompression encoding endpoints use only standard Lean axioms."

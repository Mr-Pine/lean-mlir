import SSA.Projects.Agave.Ed25519.Proof.SHA512.Padding
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ExecutionProgram
import SSA.Projects.RIR.Tests.Syntax.SingleThreadFence

/-! Kernel axiom guard. Padding is a semantic refinement parameterized only by
complete-block compression; the exact wrapper is imported but its full memory
execution theorem is still outstanding. This audit does not discharge that gap. -/

/-- info: SHA-512 padding and exact import endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.needsTwoBlocks_iff,
    ``Agave.Ed25519.SHA512.bitLength_arithmetic,
    ``Agave.Ed25519.SHA512.finalBlocks_whole,
    ``Agave.Ed25519.SHA512.finalBlocks_flatten,
    ``Agave.Ed25519.SHA512.finalBlocks_fold,
    ``Agave.Ed25519.SHA512.finalize_eq_digest,
    ``Agave.Ed25519.SHA512.finalize_transcript,
    ``Agave.Ed25519.SHA512.digest_eq_of_block_agrees,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.block_count,
    ``LeanMLIR.RIR.Instr.run_fenceSingleThread,
    ``LeanMLIR.RIR.Tests.Syntax.SingleThreadFence.instruction_run]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SHA-512 padding and exact import endpoints use only standard Lean axioms."

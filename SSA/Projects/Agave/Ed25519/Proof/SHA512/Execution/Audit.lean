import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Allocation
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.BranchContracts
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ContextContracts
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail

/-! Guarded dependency audit for checked pieces of the actual finalizer.
This does not assert the outstanding bb3 serialization/reduction/zeroization
execution, padding-memory readback, or a complete `Func.call` contract. -/

/-- info: SHA-512 finalizer execution pieces use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.oneBlock_of_compress,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.reduceWide_output,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.bitLength_wrapping,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.pending_zext128,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.pending_zext64,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.pending_shift,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.bitLength_disjoint,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.bitLength_or_defined,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.reduceWide_unrestricted,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.scalarFromSha512_unrestricted,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.allocateSlots_wf,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.allocateSlots_counter,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.allocateSlots_live,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.allocateSlots_slot_live,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.allocateSlots_read,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.allocateSlots_frame,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.zeroBytes_frame,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.allocation_prefix,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.short_block,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.long_block,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.short_block_of_contract,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.long_block_of_contract,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.padding_tail]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SHA-512 finalizer execution pieces use only standard Lean axioms."

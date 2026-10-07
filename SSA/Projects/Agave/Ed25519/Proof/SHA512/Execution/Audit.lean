import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Allocation
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.BranchContracts
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ContextContracts
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.FullCall

/-! Guarded dependency audit for the actual four-block finalizer, including
serialization, all zeroization stores, padding readback, and full call cleanup.
Compression and exact linked wide-reducer execution remain explicit local
premises of the composition theorems; they are not asserted by this audit. -/

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
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.padding_tail,
    ``Agave.Ed25519.SHA512.swapBytes128_lengthField,
    ``Agave.Ed25519.SHA512.serialize_word,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.serialization_prefix,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.serialized_readback,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.scratch_zeroization,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.digest_zero_chunk0,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.digest_zero_chunk7,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.final_lifetimes,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.final_tail,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.padBuffer_bytes,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.paddingState_bytes,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.short_padding_readback,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.long_padding_readback,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.entry_block,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.padded_branches,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.final_block_of_contract,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.ready_of_frame,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.linkedReduceWide_of_execution,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.finalizer_run,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.finalizer_contract_under,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.finalizer_contract,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.linked_finalizer_contract,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.linked_finalizer_of_execution]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SHA-512 finalizer execution pieces use only standard Lean axioms."

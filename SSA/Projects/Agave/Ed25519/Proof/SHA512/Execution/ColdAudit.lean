import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdLinked

/-! Guarded dependency audit of the cold-cache finalizer and challenge-call
composition. The compressor execution obligation remains an explicit local premise. The
strongest linked endpoint uses the proved complete scalar-reducer call. -/

/-- info: Cold SHA-512 finalizer and challenge composition use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFrame.trans,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFrame.storeAt,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFrame.eraseFrom,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFramedStoreEffect.cacheOutput,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheOutputEffect.warm,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheOutputEffect.challenge_regions,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheOutputEffect.challenge_boolean,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.short_block_cold,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.long_block_cold,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.padded_branches_cold,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.finalizer_run_cold,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.finalizer_contract_cold,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.finalizer_call_warm,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.linked_finalizer_cold,
    ``Agave.Ed25519.Verifier.Execution.Challenge.compress_blocks_cold,
    ``Agave.Ed25519.Verifier.Execution.Challenge.tail_reaches_final_cold,
    ``Agave.Ed25519.Verifier.Execution.Challenge.remaining_reaches_final_cold,
    ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_reaches_final_cold,
    ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_run_cold,
    ``Agave.Ed25519.Verifier.Execution.Challenge.challenge_call_cold,
    ``Agave.Ed25519.Verifier.Execution.Challenge.coldLinked_finalizer_contract,
    ``Agave.Ed25519.Verifier.Execution.Challenge.coldLinked_finalizer_contract_proved]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Cold SHA-512 finalizer and challenge composition use only standard Lean axioms."

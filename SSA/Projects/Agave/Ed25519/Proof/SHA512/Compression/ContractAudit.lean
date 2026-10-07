import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizerContracts

/-! Kernel axiom audit of the contextual memory rules. These are structural
contract implications, not a proof that an imported backend meets the contract. -/

/-- info: SHA-512 contextual memory rules use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CompressionReady.storeAt,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CompressionReady.alloca,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CompressionReady.of_frame,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CompressionReady.frame_then_output,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheTransition.trans,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.cache_store_same,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFramedStoreEffect.to_storeEffect,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFramedStoreEffect.ready,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFramedStoreEffect.read_disjoint,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFramedStoreEffect.cache_transition,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.CacheFramedStoreEffect.boolean_observation,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.compress_count_bound,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.oneBlock_of_compress_under,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.compress_warm,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.scalarFromSha512_warm,
    ``Agave.Ed25519.Verifier.Execution.SHA512Finalization.scalarFromSha512_boolean_observation]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SHA-512 contextual memory rules use only standard Lean axioms."

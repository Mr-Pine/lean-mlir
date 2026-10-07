import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialPrefixShape

/-! The final readiness endpoint still assumes: exact challenge/decode linkage;
SHA CompressContractUnder; EntryMemory and ColdEntryReady for this invocation;
serial table/cache separation and initial serial Ready; the concrete prefix's
hardware InstructionContracts and LinkedPrefix; and DecoderSemantic.PrefixBoundary
only after an actual ColdCallTrace. No ShapeAt, complete backend execution,
whole decoder result, or arbitrary-state serial readiness premise remains.
-/

/-- info: Exact verifier prefix allocation shape uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.allocationShape_at_of_cacheOutputEffect,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.globalShape_of_cacheOutputEffect,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.decoder_allocationShape_of_prefix,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.challenge_allocationShape_at,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.shapeAt_of_decoder_prefix,
    ``Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness.coldReady_of_decoder_prefix]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact verifier prefix allocation shape uses only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchLinked

/-! Kernel audit of concrete scalar/AVX2 count-one dispatch and finalization,
and the conditional adapter isolating the direct arbitrary-count AVX2 equation.
Hardware instruction laws remain explicit parameters, as does the stated bulk
backend premise of the bulk adapter; neither is silently axiomatized. -/

/-- info: Linked SHA-512 finalization and conditional bulk dispatch use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.initialized_ready,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.initialized_warm,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.initialized_callReady,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.initialized_cache_read,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.initialized_chain_read,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.initialized_data_read,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.public_store_effect,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.initialized_effect,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.effect_erase,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.call_of_run_effect,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.scalarSuffix_before,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.dispatch_entry_constants,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.dispatch_entry_zero,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.scalar_suffix,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.selected_suffix,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.dispatch_run_at,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.dispatch_contract_at,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.dispatch_contract_of_avx2,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.dispatch_oneBlock_of_avx2,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.shaInitializer_eq,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.linked_initializer,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.linked_oneBlock_contract,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.linked_finalizer_contract,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.avx2_contract_of_call_equation,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.linked_compress_contract,
    ``Agave.Ed25519.SHA512.Execution.Dispatch.Finalization.linked_compress_contract_of_avx2]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Linked SHA-512 finalization and conditional bulk dispatch use only standard Lean axioms."

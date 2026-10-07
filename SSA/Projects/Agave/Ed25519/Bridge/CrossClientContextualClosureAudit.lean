import SSA.Projects.Agave.Ed25519.Bridge.CrossClientParameterizedCallerUnder
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBackendLeaves

/-! Audit the complete contextual propagation and actual backend witnesses.
Ready predicates remain visible theorem arguments, never introduced axioms. -/

/-- info: Contextual backend composition retains exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalar_check_of_contracts_trace,
    ``Agave.Ed25519.Verifier.Execution.Dalek.point_check_of_contracts_trace,
    ``Agave.Ed25519.Verifier.Execution.Dalek.entry_of_sha_contracts_cold_trace,
    ``Agave.Ed25519.Verifier.Execution.Dalek.backend_tail_of_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.dispatch_tail_of_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.initialized_tail_of_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.copy_tail_of_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.scalar_tail_of_nondecoder_contracts_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.body_of_contextual_contracts,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_from_entry_of_leaf_contracts_cold_under,
    ``Agave.Ed25519.Verifier.Execution.Dalek.program_call_of_leaf_contracts_cold_under,
    ``Agave.Ed25519.Verifier.Execution.ResidualLeaves.NonDecoderContractsUnder.complete,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder.primitive_calls,
    ``Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder.observe,
    ``Agave.Ed25519.Bridge.firedancerSourceReduce_correct,
    ``Agave.Ed25519.Bridge.firedancerReductionValueCorrect_of_call,
    ``Agave.Ed25519.Bridge.BackendLeaves.RemainingContracts.complete,
    ``Agave.Ed25519.Bridge.contextual_cold_crossClient_observations,
    ``Agave.Ed25519.Bridge.parameterized_contextual_cold_crossClient_observations,
    ``Agave.Ed25519.Bridge.parameterized_contextual_cold_crossClient_of_canonical,
    ``Agave.Ed25519.Bridge.parameterizedCaller_contextual_cold_crossClient_observations,
    ``Agave.Ed25519.Bridge.parameterizedCaller_contextual_cold_crossClient_of_canonical]
  for target in targets do
    let actual := (← collectAxioms target).toList
    unless actual.length == expected.length && expected.all actual.contains do
      throwError "Unexpected axioms for {target}: {actual}"
  let legacy := expected ++ [
    `Firedancer.Common.fd_sha512_init,
    `Firedancer.Common.fd_sha512_append,
    `Firedancer.Common.fd_sha512_fini]
  let actual := (← collectAxioms
    ``Agave.Ed25519.Bridge.FiredancerProofInvocation.challenge_eq_of_proved_reducer).toList
  unless actual.length == legacy.length && legacy.all actual.contains do
    throwError "Unexpected legacy invocation arithmetic adapter axioms: {actual}"
  logInfo "Contextual backend composition retains exactly the three standard foundations."

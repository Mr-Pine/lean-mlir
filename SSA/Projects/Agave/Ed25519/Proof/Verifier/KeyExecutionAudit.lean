import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionContracts
import SSA.Projects.Agave.Ed25519.Proof.Verifier.KeyExecutionNegation

/-- info: Key constructor execution endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Key.entry_block,
    ``Agave.Ed25519.Verifier.Execution.Key.reject_block,
    ``Agave.Ed25519.Verifier.Execution.Key.return_block,
    ``Agave.Ed25519.Verifier.Execution.Key.success_block,
    ``Agave.Ed25519.Verifier.Execution.Key.run_of_decoder,
    ``Agave.Ed25519.Verifier.Execution.Key.call_of_decoder,
    ``Agave.Ed25519.Verifier.Execution.Key.observe_of_decoder,
    ``Agave.Ed25519.Verifier.Execution.Key.wrapper_keyCall,
    ``Agave.Ed25519.Verifier.Execution.Key.observe_refines,
    ``Agave.Ed25519.Verifier.Execution.Key.negResult_value,
    ``Agave.Ed25519.Verifier.Execution.Key.negResult_tight]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Key constructor execution endpoints use only standard Lean axioms."

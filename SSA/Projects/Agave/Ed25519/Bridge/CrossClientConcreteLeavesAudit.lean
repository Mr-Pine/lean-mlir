import SSA.Projects.Agave.Ed25519.Bridge.CrossClientConcreteLeaves

/-! A standard-foundation audit does not discharge explicit hypotheses.
The residual semantic contracts are documented separately in the ledger. -/

/-- info: Concrete-payload cross-client endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.ResidualLeaves.scalarChallenge_encoding,
    ``Agave.Ed25519.Verifier.Execution.ResidualLeaves.Contracts.complete,
    ``Agave.Ed25519.Verifier.Execution.ValidPoint.negate,
    ``Agave.Ed25519.Verifier.Execution.ValidPoint.shared_correct,
    ``Agave.Ed25519.Verifier.Execution.ValidPoint.parser_contracts,
    ``Agave.Ed25519.Verifier.Execution.LinkedValidPayload.exactSignatureInputs_of_decoder,
    ``Agave.Ed25519.Bridge.concreteLeaves_crossClient_observations,
    ``Agave.Ed25519.Bridge.concreteLeaves_crossClient_of_canonical]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Concrete-payload cross-client endpoints use only standard Lean axioms."

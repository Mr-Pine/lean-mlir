import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedConcretePayload

/-- info: Concrete linked cached-point transport uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.LinkedConcretePayload.copiedKey_point,
    ``Agave.Ed25519.Verifier.Execution.LinkedConcretePayload.afterSignature_point,
    ``Agave.Ed25519.Verifier.Execution.LinkedConcretePayload.signatureMemory_of_decoder,
    ``Agave.Ed25519.Verifier.Execution.LinkedConcretePayload.exactSignatureInputs_of_decoder,
    ``Agave.Ed25519.Verifier.Execution.LinkedConcretePayload.observe_of_decoder]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Concrete linked cached-point transport uses only standard Lean axioms."

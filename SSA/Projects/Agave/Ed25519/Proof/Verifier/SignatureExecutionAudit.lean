import SSA.Projects.Agave.Ed25519.Proof.Verifier.SignatureExecution

/-- info: Signature constructor execution endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Signature.program_call,
    ``Agave.Ed25519.Verifier.Execution.Signature.copied_wf,
    ``Agave.Ed25519.Verifier.Execution.Signature.copied_smallRange,
    ``Agave.Ed25519.Verifier.Execution.Signature.copied_read_frame,
    ``Agave.Ed25519.Verifier.Execution.Signature.copied_read_R,
    ``Agave.Ed25519.Verifier.Execution.Signature.copied_read_S,
    ``Agave.Ed25519.Verifier.Execution.Signature.wrapper_signature,
    ``Agave.Ed25519.Verifier.Execution.Signature.wrapper_successCalls]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Signature constructor execution endpoints use only standard Lean axioms."

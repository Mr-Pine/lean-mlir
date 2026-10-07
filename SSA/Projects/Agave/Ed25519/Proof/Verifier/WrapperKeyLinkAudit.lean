import SSA.Projects.Agave.Ed25519.Proof.Verifier.WrapperKeyLink

/-- info: Exact key-to-wrapper links use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.WrapperKeyLink.output_fits,
    ``Agave.Ed25519.Verifier.Execution.WrapperKeyLink.erase_fits,
    ``Agave.Ed25519.Verifier.Execution.WrapperKeyLink.key_memory,
    ``Agave.Ed25519.Verifier.Execution.WrapperKeyLink.primitive_calls_of_decoder,
    ``Agave.Ed25519.Verifier.Execution.WrapperKeyLink.observe_of_decoder_calls,
    ``Agave.Ed25519.Verifier.Execution.WrapperKeyLink.refines_of_decoder_calls]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Exact key-to-wrapper links use only standard Lean axioms."

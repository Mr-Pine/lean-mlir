import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SemanticAdapter

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.run
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.observe
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.simulates_iff_digest
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.digestBy_of_simulates
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.ready_executionRefines_of_digest_simulation

/-- info: Firedancer SHA semantic adapter uses only standard Lean axioms; its verifier endpoint uses exactly the standard three. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.observe,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.Correct,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.Simulates,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.simulates_iff_digest,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation.digestBy_of_simulates,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.ready_executionRefines_of_digest_simulation]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  let actual := (← collectAxioms
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.ready_executionRefines_of_digest_simulation).toList
  unless actual.length == allowed.length && allowed.all actual.contains do
    throwError "Unexpected semantic adapter execution axiom inventory: {actual}"
  logInfo "Firedancer SHA semantic adapter uses only standard Lean axioms; its verifier endpoint uses exactly the standard three."

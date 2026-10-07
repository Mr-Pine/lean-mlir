import SSA.Projects.Agave.Ed25519.Bridge.CrossClientPointwiseDigest

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.ready_executionRefines_of_transcript
#print axioms Agave.Ed25519.Bridge.pointwise_cold_crossClient_observations
#print axioms Agave.Ed25519.Bridge.pointwise_cold_crossClient_of_canonical
#print axioms Agave.Ed25519.Bridge.pointwise_cold_crossClient_runs
#print axioms Agave.Ed25519.Bridge.pointwise_cold_crossClient_runs_of_canonical

/-- info: Pointwise cross-client observations use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for endpoint in
      [``Agave.Ed25519.Bridge.FiredancerSHAExecution.ready_executionRefines_of_transcript,
       ``Agave.Ed25519.Bridge.pointwise_cold_crossClient_observations,
       ``Agave.Ed25519.Bridge.pointwise_cold_crossClient_of_canonical,
       ``Agave.Ed25519.Bridge.pointwise_cold_crossClient_runs,
       ``Agave.Ed25519.Bridge.pointwise_cold_crossClient_runs_of_canonical] do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
    let declaration ← getConstInfo endpoint
    if (declaration.type.find? (fun e =>
        e.isConstOf ``Agave.Ed25519.Bridge.Challenge.DigestBy)).isSome then
      throwError "Uniform DigestBy premise remains in {endpoint}"
  logInfo "Pointwise cross-client observations use only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Bridge.CrossClientSHAComplete

/-- info: Concrete SHA verifier readiness uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoint := ``Agave.Ed25519.Verifier.Execution.BackendReadiness.inputs_of_linked_sha
  for dependency in (← collectAxioms endpoint) do
    unless allowed.contains dependency do
      throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Concrete SHA verifier readiness uses only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.Verifier.BcmpBoundary

/-- info: All four invocation-local bcmp boundary endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.FramedInvocation.toInvocation,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.of_compare_contract,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.compression_tail_of_invocation,
    ``Agave.Ed25519.Verifier.Execution.Dalek.Bcmp.compression_tail_of_framed_invocation]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "All four invocation-local bcmp boundary endpoints use only standard Lean axioms."

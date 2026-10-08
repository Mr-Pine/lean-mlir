import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachableConcrete
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachablePrefixAudit

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierTailCalls
#print axioms Agave.Ed25519.Bridge.CrossClientReachableConcrete.observations
#print axioms Agave.Ed25519.Bridge.CrossClientReachableConcrete.observations_of_canonical
#print axioms Agave.Ed25519.Bridge.CrossClientReachableConcrete.runs

/-- info: Closed actual-source cross-client comparison uses exactly the three standard foundations. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let expected : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierTailCalls,
    ``Agave.Ed25519.Bridge.CrossClientReachableConcrete.observations,
    ``Agave.Ed25519.Bridge.CrossClientReachableConcrete.observations_of_canonical,
    ``Agave.Ed25519.Bridge.CrossClientReachableConcrete.runs]
  for target in targets do
    let actual := (← collectAxioms target).toList
    unless actual.length == expected.length && expected.all actual.contains do
      throwError "Unexpected closed cross-client source axioms for {target}: {actual}"
  logInfo "Closed actual-source cross-client comparison uses exactly the three standard foundations."

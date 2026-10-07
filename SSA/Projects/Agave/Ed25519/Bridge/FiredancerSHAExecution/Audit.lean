import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Linked

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.body
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.run
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.call
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_wf
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_other_block
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.zero_eval
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.zero_run
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.zero_call
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.constants_eq_standard
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.constants_install_wf
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.constants_install_read
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.append_empty_call

/-- info: Firedancer SHA execution endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.memory_other_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.zero_eval,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.zero_run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Append.zero_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.constants_eq_standard,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.constants_install_wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.constants_install_read,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.append_empty_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Init.program,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.program,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.appendProgram,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.finishProgram]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer SHA execution endpoints use only standard Lean axioms."

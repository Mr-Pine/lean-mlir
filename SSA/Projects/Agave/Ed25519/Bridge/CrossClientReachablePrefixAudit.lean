import SSA.Projects.Agave.Ed25519.Bridge.CrossClientReachablePrefix
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachablePrefixRepresents

/-- info: Concrete source prefix and cross-client prefix bridge use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierInitialBlock_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAfterR_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAfterA_represents,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierInitialBlock_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierInitialBlock_count,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAfterR_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAfterA_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAfterR_count,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAfterA_count,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAppendR,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.verifierAppendA,
    ``Agave.Ed25519.Bridge.CrossClientReachablePrefix.observations,
    ``Agave.Ed25519.Bridge.CrossClientReachablePrefix.observations_of_canonical,
    ``Agave.Ed25519.Bridge.CrossClientReachablePrefix.runs]
  for target in targets do
    for dependency in (← collectAxioms target) do
      unless allowed.contains dependency do
        throwError "Unexpected prefix bridge axiom {dependency} in {target}"
  logInfo "Concrete source prefix and cross-client prefix bridge use only standard Lean axioms."

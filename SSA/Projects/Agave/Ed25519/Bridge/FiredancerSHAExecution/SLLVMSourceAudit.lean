import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInitObservation

/-! Strict transitive audit of the source CFG values and checked initializer
call/frame/observation theorems. This does not certify append/core/finish
correctness; those imported bodies are values rather than execution proofs. -/

/-- info: SLLVM SHA source values and initializer proofs use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.init,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.core,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.append,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.finish,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.programs,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.init_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.init_call,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.initMemory_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.initMemory_other,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.init_contract,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.rir_storeAt_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.rir_initMemory_block,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.initObserve_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.rirInitObserve_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.init_call_observation_eq]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "SLLVM SHA source values and initializer proofs use only standard Lean axioms."

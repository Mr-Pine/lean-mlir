import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreCorrect

/-! Strict transitive axiom audit of actual source SHA compression execution,
all loop inductions, native-byte observations, and the caller memory frame. -/

/-- info: Actual SLLVM SHA core execution uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.SmallRange.add,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.SmallRange.afterAlloca,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.run_load_readBits,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.entry_cont,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.first_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.later_body,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.feedforward_step,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.outer_run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.done_run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.first_run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.later_run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.feedforward_run,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.input_swap_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.constants_word,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.RingWrites.wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.feedforwardMemory_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.pack_chainState,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.readBytes_splice_disjoint,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.readBytes_blocks_succ,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.scratch_popFrame_live,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.later_suffix,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.first_suffix,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.eighty_rounds,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.outer_step,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.outer_blocks,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core.executes]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Actual SLLVM SHA core execution uses only standard Lean axioms."

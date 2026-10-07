import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreInductionAudit
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreMultiBlocks

/-! Strict transitive axiom closure for native stores and positive-count outer
loop induction. Full call entry and cleanup are audited by their owner. -/
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_outer_blocks

/-- info: Firedancer multi-block execution uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforwardMemory_eq,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforwardMemory_read,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforwardMemory_bytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.chainMemory_of_packed,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforwardMemory_chain,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.outer_more_test,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.feedforward_backedge,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.outer_next_pointers,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.outer_next_firstReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.storeAt_overwrite,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.input_tail_disjoint,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.run_readBytes_cons,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.core_outer_blocks ]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer multi-block execution uses only standard Lean axioms."

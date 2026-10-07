import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreEightyRounds

/-! Strict transitive standard-three axiom audit of the actual eighty-round
execution proof and its local definitions. This does not assert closure of the
outer call, which is a separate proof. -/

#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.eighty_rounds
#print axioms Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.eighty_from_input

/-- info: Firedancer eighty-round execution uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.params2,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.params3,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.params4,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstNextEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterNextEnv,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FinalReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstNext_ready,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterNext_ready,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_backedge,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_exit,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_backedge,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_exit,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_final_ready,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LoopFrame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LoopFrame.refl,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LoopFrame.trans,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LoopFrame.write,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LoopFrame.read_val,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstBody_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstNext_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterBody_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterNext_frame,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterLoopReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.laterNext_loopReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterMemory.step,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites.trans,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites.readAt,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterTrace,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterTrace.runFrom,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.LaterTrace.evalFrom,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_suffix,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.later_sixtyfour,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstLoopReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstLoopReady.one,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstMemory,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstMemory.word,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstMemory.step,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstMemory.complete,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstNext_loopReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.firstExit_loopReady,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstTrace,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstTrace.runFrom,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.FirstTrace.evalFrom,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.first_suffix,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites.alloc,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites.wf,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites.smallRange,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites.eraseFrom,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.RingWrites.readBytes,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.EightyTrace,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.EightyTrace.runFrom,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.EightyTrace.evalFrom,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.eighty_rounds,
    ``Agave.Ed25519.Bridge.FiredancerSHAExecution.Core.eighty_from_input ]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Firedancer eighty-round execution uses only standard Lean axioms."

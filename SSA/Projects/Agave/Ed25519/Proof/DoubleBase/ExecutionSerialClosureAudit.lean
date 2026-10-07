import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialDalekAdapter
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLinkedCalls

/-- info: Serial whole-call closure uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.DoubleBase.RIR.serialLinked_ladderHelpers,
    ``Agave.Ed25519.DoubleBase.RIR.serial_ladder_cached_sub,
    ``Agave.Ed25519.DoubleBase.RIR.serial_ladder_cached_add,
    ``Agave.Ed25519.DoubleBase.RIR.serial_ladder_affine_sub,
    ``Agave.Ed25519.DoubleBase.RIR.serial_ladder_affine_add,
    ``Agave.Ed25519.DoubleBase.RIR.serial_ladder_round,
    ``Agave.Ed25519.DoubleBase.RIR.serial_ladder_run,
    ``Agave.Ed25519.DoubleBase.RIR.serialLinked_ladder_run_validPoint,
    ``Agave.Ed25519.DoubleBase.RIR.serialLinked_run_validPoint,
    ``Agave.Ed25519.DoubleBase.RIR.serialLinked_call_validPoint,
    ``Agave.Ed25519.DoubleBase.RIR.serialLinked_dalek_call]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Serial whole-call closure uses only standard Lean axioms."

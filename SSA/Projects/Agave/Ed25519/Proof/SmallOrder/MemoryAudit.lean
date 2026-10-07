import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityAllocation
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityProducts
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointOutput
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoubleWord
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoubleStores

/-- info: Small-order MemoryAudit endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SmallOrder.Execution.EqualityAllocation.prepare_run,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityAllocation.allocated_frame,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.productsX_run,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.productsY_run,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.productsX_private,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.productsY_private,
    ``Agave.Ed25519.SmallOrder.Execution.pointStore_readback,
    ``Agave.Ed25519.SmallOrder.Execution.pointStore_frame,
    ``Agave.Ed25519.SmallOrder.Execution.DoublePhases.store_payload_run]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Small-order MemoryAudit endpoints use only standard Lean axioms."

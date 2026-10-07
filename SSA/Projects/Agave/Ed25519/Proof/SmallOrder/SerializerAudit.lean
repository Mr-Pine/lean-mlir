import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerXL
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerXR
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerYL
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerYR

/-- info: Small-order SerializerAudit endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SmallOrder.Execution.Transport.Renaming.run,
    ``Agave.Ed25519.SmallOrder.Execution.Transport.Renaming.fold,
    ``Agave.Ed25519.SmallOrder.Execution.Transport.Renaming.fold_success,
    ``Agave.Ed25519.SmallOrder.Execution.Transport.Embedding.write,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerSource.core_run,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerXL.body_alpha,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerXL.inline_run,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerXR.body_alpha,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerXR.inline_run,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerYL.body_alpha,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerYL.inline_run,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerYR.body_alpha,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerYR.inline_run]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Small-order SerializerAudit endpoints use only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerAudit
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.MemoryAudit
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.FieldProduct
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityTail
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.ExecutionGaps
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityPhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityCompare
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoubleAdapter
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoublePhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoubleSquarePhases
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorCall
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.FirstSerializerInitialization
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerFrames

/-! This guard checks only the named local and phase-composition theorems.
Neither CofactorExecutionGap nor EqualityExecutionGap has a proof in this batch. -/

/-- info: Small-order local and phase endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.SmallOrder.eightTimes_tight,
    ``Agave.Ed25519.SmallOrder.eightTimes_value,
    ``Agave.Ed25519.SmallOrder.doubleCompleted_ignores_T,
    ``Agave.Ed25519.SmallOrder.machineBytes_eq_iff,
    ``Agave.Ed25519.SmallOrder.serialized_crossEqual,
    ``Agave.Ed25519.SmallOrder.Execution.field_product_call,
    ``Agave.Ed25519.SmallOrder.Execution.cofactor_is_imported,
    ``Agave.Ed25519.SmallOrder.Execution.equality_is_imported,
    ``Agave.Ed25519.SmallOrder.Execution.equalityTail_run,
    ``Agave.Ed25519.SmallOrder.Execution.linked_equalityTail_run,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.runFrom_of_phases,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.call_of_phases,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.linked_compareX_run,
    ``Agave.Ed25519.SmallOrder.Execution.EqualityPhases.linked_compareY_run,
    ``Agave.Ed25519.SmallOrder.Execution.square_adapter_call,
    ``Agave.Ed25519.SmallOrder.Execution.projective_double_adapter_program,
    ``Agave.Ed25519.SmallOrder.Execution.projective_double_program,
    ``Agave.Ed25519.SmallOrder.Execution.DoublePhases.runFrom_of_phases,
    ``Agave.Ed25519.SmallOrder.Execution.DoublePhases.squareX_run,
    ``Agave.Ed25519.SmallOrder.Execution.DoublePhases.squareY_run,
    ``Agave.Ed25519.SmallOrder.Execution.DoublePhases.squareZ_run,
    ``Agave.Ed25519.SmallOrder.Execution.DoublePhases.squareSum_run,
    ``Agave.Ed25519.SmallOrder.Execution.CofactorPhases.first_loop_edge,
    ``Agave.Ed25519.SmallOrder.Execution.CofactorPhases.second_loop_edge,
    ``Agave.Ed25519.SmallOrder.Execution.CofactorPhases.runFrom_of_phases,
    ``Agave.Ed25519.SmallOrder.Execution.CofactorPhases.call_of_phases,
    ``Agave.Ed25519.SmallOrder.Execution.firstSerializer_ready,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerXL.frame,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerXR.frame,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerYL.frame,
    ``Agave.Ed25519.SmallOrder.Execution.SerializerYR.frame]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "Small-order local and phase endpoints use only standard Lean axioms."

import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialDalekAdapter
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekDoubleBaseContractUnder

/-! The proved serial call in the shared verifier contract interface.
Readiness contains concrete initial globals only. The contextual constructor
contract is the sole remaining execution leaf. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open Verifier Verifier.Execution

/-- Exact globals read by the serial normal path and its constructor. -/
def serialLinkedReady (g : SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (_out _hptr _aptr _sptr : Pointer) (s : GlobalState) : Prop :=
  SerialContracts.GlobalsReady g s ∧ Tables.SerialConstructorContext.GlobalsReady d2 s

/-- Shared Dalek contract for the exact serial CFG and linked callees.
All local point helpers, digit bounds, loop execution, output validity,
exact output bytes, and caller-memory preservation are proved. -/
theorem serialLinked_doubleBaseContractUnder (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (cofactor : ValidPoint → ValidPoint)
    (htable : Tables.SerialConstructorContext.ContextualTableContract d2
      (serialLinkedPrimitives d2 panic).call0) :
    Dalek.DoubleBaseContractUnder (serialLinkedReady g d2) (serialLinkedKernel g d2 panic).call
      (ValidPoint.layout cofactor) ValidPoint.doubleBase := by
  intro out hptr aptr sptr state hval sval aval hwf hr hout hh ha hs _ _ _
  exact serialLinked_dalek_call g d2 panic htable out hptr aptr sptr state hval sval aval
    hwf hout hh ha hs hr.2 hr.1

end Agave.Ed25519.DoubleBase.RIR

/-- info: Serial Dalek contract uses only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for dependency in (← collectAxioms
      ``Agave.Ed25519.DoubleBase.RIR.serialLinked_doubleBaseContractUnder) do
    unless allowed.contains dependency do
      throwError "Unexpected axiom {dependency} in serial Dalek contract"
  logInfo "Serial Dalek contract uses only standard Lean axioms."

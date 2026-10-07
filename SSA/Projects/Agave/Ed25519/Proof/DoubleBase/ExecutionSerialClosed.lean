import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialDalekContract
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorContract

/-! The complete linked serial double-base call has no residual execution
premise. The initial identity, fixed base table and 2d bytes remain ordinary
contextual memory facts. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open Verifier Verifier.Execution

/-- All helper contracts, including the concrete table constructor, are
closed by their checked imported execution proofs. -/
theorem serialLinked_doubleBaseContractUnder_closed (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (cofactor : ValidPoint → ValidPoint) :
    Dalek.DoubleBaseContractUnder (serialLinkedReady g d2) (serialLinkedKernel g d2 panic).call
      (ValidPoint.layout cofactor) ValidPoint.doubleBase :=
  serialLinked_doubleBaseContractUnder g d2 panic cofactor
    (Tables.SerialConstructorContract.linked_contract d2 panic)

/-- Exact caller-visible execution and bytes for the concrete serial backend.
There is no constructor, point-helper, loop, output or success assumption. -/
theorem serialLinked_dalek_call_closed (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (out hptr aptr sptr : Pointer) (state : GlobalState)
    (hval sval : CanonicalScalar) (aval : ValidPoint)
    (hwf : state.WF) (hout : NAF.Memory.Buffer state.mem out 160)
    (hh : Dalek.ReadBytes state hptr 32 (CanonicalScalar.encode hval))
    (hA : Dalek.ReadBytes state aptr 160 aval.bytes)
    (hs : Dalek.ReadBytes state sptr 32 (CanonicalScalar.encode sval))
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 state)
    (hg : SerialContracts.GlobalsReady g state) :
    ∃ after encoded,
      (serialLinkedKernel g d2 panic).call (Dalek.args4 out hptr aptr sptr) state =
        .value (.nil, after) ∧
      Dalek.OutputFrame state after out 160 ∧ Dalek.ReadBytes after out 160 encoded ∧
      ValidPoint.ResultRepresents (ValidPoint.doubleBase hval aval sval) encoded :=
  serialLinked_dalek_call g d2 panic (Tables.SerialConstructorContract.linked_contract d2 panic)
    out hptr aptr sptr state hval sval aval hwf hout hh hA hs hd2 hg

end Agave.Ed25519.DoubleBase.RIR

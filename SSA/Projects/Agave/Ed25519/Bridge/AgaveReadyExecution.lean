import SSA.Projects.Agave.Ed25519.Bridge.AgaveReadyInputs
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientChallengeValue

/-! Complete Agave verification under ordinary caller/environment conditions.
`CallerMemory` contains WF, public-key/signature/message live ranges and their
bytes, the ABI length equation, and the machine message-length bound.
`InitializedGlobals` contains the identity, SHA IV and round constants, caches,
Montgomery and decoder constants, and cache separation. Serial/AVX readiness
contains only loaded tables/constants and their addresses. Hardware laws cover
CPUID, gated XGETBV and cache stores. The only external function contract is
bcmp; there is no assumed decoder, hash, backend, prefix or whole-verifier run. -/
namespace Agave.Ed25519.Bridge.AgaveReady
open Verifier Verifier.Execution
open LeanMLIR.RIR
open Dalek.SerialBackendReadiness (Ready Separate)
open Agave.Ed25519.SHA512.Execution.Dispatch
set_option maxRecDepth 24000
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

/-- Mathematical strict Ed25519 verification with the standard SHA-512 compression. -/
noncomputable def strictVerify (a r s : Bytes32) (message : List (BitVec 8)) : Bool :=
  decide (AgaveStrictAccept a r s.toNat
    (messageChallenge (SHA512.model SHA512.Spec.compression).digest r a message))

theorem verify_eq_strict (a r s : Bytes32) (message : List (BitVec 8)) :
    verify (ValidPoint.shared Encoding.Decompress.Valid.decode) ValidPoint.doubleBase compress a r s
      (ResidualLeaves.scalarChallenge (SHA512.model SHA512.Spec.compression) r a message) =
      strictVerify a r s message := by
  apply Bool.eq_iff_iff.mpr
  simpa only [strictVerify, decide_eq_true_eq, agave_scalarChallenge_eq_messageChallenge] using
    verify_iff_strict_accept_represented (ValidPoint.shared Encoding.Decompress.Valid.decode)
      ValidPoint.curve Fin.val
      (ValidPoint.shared_correct Encoding.Decompress.Valid.decode Encoding.Decompress.Valid.decoderCorrect)
      ValidPoint.doubleBase id compress (fun _ _ _ _ _ => rfl) (fun _ => rfl)
      a r s (ResidualLeaves.scalarChallenge (SHA512.model SHA512.Spec.compression) r a message)
      (CanonicalScalar.bound _)

section
variable (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
variable (serialGlobals : DoubleBase.SerialCFG.Globals)
variable (d2 : Tables.SerialConstructor.Globals) (panic : DoubleBase.RIR.SerialPanic)
variable (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
variable (avx2Globals : DoubleBase.Avx2CFG.Globals)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)

variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (hbcmp : Dalek.CompareContract remaining.compareBytes)
variable (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
variable (hcaller : ColdInput.CallerMemory i initial a r s message)
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
include hhardware hbcmp hcaller hglobals hserial havxGlobals hseparate havxSeparate

/-- Construct all actual wrapper primitive-call witnesses from raw memory. -/
theorem primitive_calls :
    Wrapper.PrimitiveCalls (wrapper remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)
      (ValidPoint.shared Encoding.Decompress.Valid.decode) ValidPoint.doubleBase compress
      (ResidualLeaves.scalarChallenge (SHA512.model SHA512.Spec.compression))
      i initial a r s message :=
  LinkedColdLeavesGuarded.primitive_calls (LinkedColdLeaves.keyPrimitives ddg dsg)
    (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
    dg (Finalization.linkedCall hardware scg) SHA512.Spec.compression cg sg scg ddg dsg
    Encoding.Decompress.Valid.decode SmallOrder.ValidPoint.timesEight
    (DoubleBase.RIR.serialLinkedReady serialGlobals d2) (BackendLeaves.avx2Ready avx2Globals)
    (ContextualProvedLeaves.RemainingContracts.complete remaining dg hardware serialGlobals d2 panic
      avx2Panic avx2Globals Encoding.Decompress.Valid.decode ⟨hbcmp⟩ hhardware)
    (Encoding.Decompress.Execution.Decode.ReadySemantic.contractUnder ddg dsg _)
    (Finalization.Complete.linked_compress_contract hardware hhardware scg)
    (ScalarWide.execution_obligation sg) i initial a r s message
    (inputs remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg hhardware i initial a r s message
      hcaller hglobals hserial havxGlobals hseparate havxSeparate)

/-- The actual linked wrapper terminates with the strict mathematical Boolean.
Both rejection and acceptance return defined canonical one-bit values. -/
theorem call_strict :
    ∃ finalState, (Wrapper.program (wrapper remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)).call
      i.args initial = .value (Wrapper.boolResult (strictVerify a r s message), finalState) := by
  obtain ⟨finalState, hcall⟩ := Wrapper.call_of_primitive_calls
    (wrapper remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)
    (ValidPoint.shared Encoding.Decompress.Valid.decode) ValidPoint.doubleBase compress
    (ResidualLeaves.scalarChallenge (SHA512.model SHA512.Spec.compression)) i initial a r s message
    (primitive_calls remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg hhardware hbcmp i initial a r s message hcaller hglobals hserial havxGlobals hseparate havxSeparate)
  exact ⟨finalState, hcall.trans (congrArg
    (fun b => LeanMLIR.RIR.PoisonOr.value (Wrapper.boolResult b, finalState)) (verify_eq_strict a r s message))⟩

/-- The public observation is always defined and equals strict verification. -/
theorem observe_strict :
    Execution.observe (wrapper remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg) i initial =
      some (strictVerify a r s message) := by
  have hobs := Wrapper.observe_of_primitive_calls
    (wrapper remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)
    (ValidPoint.shared Encoding.Decompress.Valid.decode) ValidPoint.doubleBase compress
    (ResidualLeaves.scalarChallenge (SHA512.model SHA512.Spec.compression)) i initial a r s message
    (primitive_calls remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg hhardware hbcmp i initial a r s message hcaller hglobals hserial havxGlobals hseparate havxSeparate)
  exact hobs.trans (congrArg some (verify_eq_strict a r s message))

end
end Agave.Ed25519.Bridge.AgaveReady

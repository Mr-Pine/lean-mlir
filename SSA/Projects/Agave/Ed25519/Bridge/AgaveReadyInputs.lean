import SSA.Projects.Agave.Ed25519.Bridge.AgaveDecoderReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchComplete
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientProvedLeavesUnder

/-! Concrete decoder, SHA and backend readiness from caller bytes and loaded
globals. All execution, exact allocation-frame and finite-prefix witnesses are
constructed inside this module. -/
namespace Agave.Ed25519.Bridge.AgaveReady
open Verifier Verifier.Execution
open LeanMLIR.RIR
open Dalek.SerialBackendReadiness (Ready Separate)
open Agave.Ed25519.SHA512.Execution.Dispatch
set_option maxRecDepth 24000
set_option maxHeartbeats 8000000

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

/-- Every implementation leaf is concrete except the external bcmp function. -/
noncomputable def primitives : Dalek.Primitives :=
  LinkedColdLeaves.primitives
    (ContextualProvedLeaves.primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals)
    (Finalization.linkedCall hardware scg) sg cg ddg dsg

noncomputable def wrapper : Wrapper.Primitives :=
  linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
    (primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)
    dg Signature.program.call

variable (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
variable (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
variable (hcaller : ColdInput.CallerMemory i initial a r s message)
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)

include hhardware hcaller hglobals

/-- A reached decoder prefix is derived from initialized constants, live
buffers and the deterministic challenge/cofactor/equality call trace. -/
theorem decoderPrefix :
    BackendReadiness.DecoderPrefix (LinkedColdLeaves.keyPrimitives ddg dsg)
      (primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)
      ddg dsg Encoding.Decompress.Valid.decode i initial a r message := by
  let hframe := ColdInput.linked_decoder_callerBlocks ddg dsg initial i a
    hcaller.wellFormed hcaller.publicKey hglobals.decoder
  obtain ⟨_, known, knownX, knownT, hk, hmemory⟩ :=
    ColdInput.inputs_of_linked_decoder dg cg sg scg ddg dsg Encoding.Decompress.Valid.decode
      SmallOrder.ValidPoint.timesEight
      (Encoding.Decompress.Execution.Decode.ReadySemantic.contractUnder ddg dsg _)
      i initial a r s message hcaller hglobals hframe
  intro decoded x t hd A hA _
  dsimp only
  intro challenged multiplied compared trace
  have hkeyState := Dalek.returnedState_eq_of_call
    (Key.call_of_decoder _ _ _ _ _ _ _ _ hd)
    (Key.call_of_decoder _ _ _ _ _ _ _ _ hk)
  have hentry : LinkedLeaves.afterSignature i initial decoded x t
      (Encoding.Decompress.Valid.decode a).isSome =
      LinkedLeaves.afterSignature i initial known knownX knownT
        (Encoding.Decompress.Valid.decode a).isSome :=
    congrArg (fun state => Signature.copied (Wrapper.copiedKey initial state)
      (Wrapper.signatureSlot initial) i.signature) hkeyState
  change Encoding.Decompress.Execution.Decode.Semantic.PrefixBoundary ddg dsg
    (Dalek.stackSlot (LinkedLeaves.afterSignature i initial decoded x t
      (Encoding.Decompress.Valid.decode a).isSome) 8) (Wrapper.signatureSlot initial) compared r
  rw [hentry] at trace ⊢
  obtain ⟨hx, ht, hy, hz, hm, hready, hdecoder⟩ := hmemory A hA
  subst knownX knownT
  have hk' : Key.DecoderCall (LinkedColdLeaves.keyPrimitives ddg dsg) (Wrapper.allocated initial) known
      (Wrapper.keyResultSlot initial) i.publicKey A.words.X A.words.T true := by simpa [hA] using hk
  have hm' : LinkedConcretePayload.SignatureMemoryExceptPoint dg cg
      (ValidPoint.layout SmallOrder.ValidPoint.timesEight)
      i initial known A.words.X A.words.T true a r s A.negate message := by simpa [hA] using hm
  have hsignature := LinkedValidPayload.signatureMemory_of_decoder _ dg cg SmallOrder.ValidPoint.timesEight
    i initial known A a r s message hk' hy hz hm'
  have hmem : Dalek.EntryMemory dg cg (ValidPoint.layout SmallOrder.ValidPoint.timesEight)
      (LinkedLeaves.afterSignature i initial known A.words.X A.words.T
        (Encoding.Decompress.Valid.decode a).isSome)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message a r s A.negate message := by
    simpa [hA] using (hsignature.continuation Signature.program.call rfl).memory
  exact Dalek.decoderPrefix_of_cold_trace
    (primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg) dg
    (LinkedColdLeaves.challengePrimitives (Finalization.linkedCall hardware scg) sg) cg sg scg
    SHA512.Spec.compression ddg dsg SmallOrder.ValidPoint.timesEight rfl
    (Finalization.Complete.linked_compress_contract hardware hhardware scg)
    (Finalization.Complete.linked_finalizer_contract hardware hhardware scg sg)
    SmallOrder.Execution.cofactorContract
    (SmallOrder.Execution.EqualityValidPoint.smallOrder_contract Encoding.Decompress.Valid.decode
      SmallOrder.ValidPoint.timesEight (fun _ => rfl))
    _ _ _ _ a r s A.negate message hmem hready hdecoder challenged multiplied compared trace

variable (hserial : Ready serialGlobals d2 initial)
variable (havxGlobals : DoubleBase.ExecutionAvx2.GlobalsReady avx2Globals initial)
variable (hseparate : Separate serialGlobals d2 dg.address1)
variable (havxSeparate : avx2Globals.address2.id ≠ dg.address1.id)
include hserial havxGlobals hseparate havxSeparate

/-- The complete guarded caller package has only raw caller/global memory
premises. No decoder prefix, exact callee frame, or backend supplier is assumed. -/
theorem inputs :
    LinkedColdLeavesGuarded.Inputs (LinkedColdLeaves.keyPrimitives ddg dsg)
      (primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)
      dg cg sg scg ddg dsg (DoubleBase.RIR.serialLinkedReady serialGlobals d2)
      (BackendLeaves.avx2Ready avx2Globals) Encoding.Decompress.Valid.decode
      SmallOrder.ValidPoint.timesEight i initial a r s message := by
  let hframe := ColdInput.linked_decoder_callerBlocks ddg dsg initial i a
    hcaller.wellFormed hcaller.publicKey hglobals.decoder
  let hdecode := Encoding.Decompress.Execution.Decode.ReadySemantic.contractUnder ddg dsg
    SmallOrder.ValidPoint.timesEight
  refine ⟨ColdInput.inputs_of_linked_decoder dg cg sg scg ddg dsg Encoding.Decompress.Valid.decode
    SmallOrder.ValidPoint.timesEight hdecode i initial a r s message hcaller hglobals hframe, ?_⟩
  exact BackendReadiness.inputs
    (primitives remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg)
    dg cg sg scg ddg dsg Encoding.Decompress.Valid.decode SmallOrder.ValidPoint.timesEight
    hardware hhardware ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ serialGlobals d2 avx2Globals
    (Finalization.linkedCall hardware scg) SHA512.Spec.compression rfl rfl
    (Finalization.Complete.linked_compress_contract hardware hhardware scg) hdecode
    i initial a r s message hcaller hglobals hframe hserial havxGlobals hseparate havxSeparate
    (decoderPrefix remaining dg hardware serialGlobals d2 panic avx2Panic avx2Globals cg sg scg ddg dsg
      hhardware i initial a r s message hcaller hglobals)

end
end Agave.Ed25519.Bridge.AgaveReady

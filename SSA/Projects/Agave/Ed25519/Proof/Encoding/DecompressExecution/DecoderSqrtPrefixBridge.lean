import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioCallFromPrefix
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixBoundary

/-! The checked decoder prefix and semantic contract reduce to one exact sqrt
prefix witness at the reached invocation. All call cleanup, caller frames,
normalized flag handling and root-representation transport are proved here. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
open Verifier.Execution.Dalek (ReadBytes)
open InlinePrefix
open SqrtRatio.CallFromPrefix (PrefixWitness)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] wordStep1 SqrtRatio.wordSqrt sqrtInputState numeratorWord denominatorWord

private theorem normalized_zero (b : Bool) :
    ((if b then 1#8 else 0#8) = 0#8 ↔ b = false) := by
  cases b <;> decide

private theorem limbBytes_payload (x : Words) : limbBytes x = fieldPayload x := rfl

/-- The remaining source-execution obligation for sqrt, under its concrete
input bytes and initialized sqrt(-1) constant. -/
def PrefixProvider (sg : SqrtRatio.Globals) : Prop :=
  ∀ (out u v : Pointer) (entry : GlobalState) (a b : Pow22501.TightWords),
    entry.WF → SmallRange entry.mem out 48 →
    ReadBytes entry u 40 (limbBytes a.limbs) →
    ReadBytes entry v 40 (limbBytes b.limbs) →
    ReadBytes entry sg.address0 40 sqrtM1.bytes →
    PrefixWitness sg out u v entry (SqrtRatio.wordSqrt a b)

theorem prefixBoundary_of_witness (dg : Globals) (sg : SqrtRatio.Globals)
    (s : GlobalState) (out input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : ReadBytes s input 32 bytes) (hout : SmallRange s.mem out 168)
    (ready : Ready dg sg s)
    (h : PrefixWitness sg (slot0 s) (slot3 s) (slot2 s) (sqrtInputState dg s input)
      (wordStep1 bytes)) : Semantic.PrefixBoundary dg sg out input s bytes := by
  have hf := sqrtInput_frame dg s input hwf
  have h0 := sqrtInput_live dg s input _ _ (slot0_live s hwf)
  obtain ⟨t,hcall,obs⟩ := SqrtRatio.CallFromPrefix.call_of_witness sg
    (slot0 s) (slot3 s) (slot2 s) (sqrtInputState dg s input) (wordStep1 bytes)
    hf.wellFormed h0 h
  have hc : (decodePrimitives sg).sqrtRatio
      (.cons (.value (slot0 s)) (.cons (.value (slot3 s)) (.cons (.value (slot2 s)) .nil)))
      (sqrtInputState dg s input) = .value (.nil,t) := hcall
  apply prefixBoundary_of_sqrt dg sg s t out input bytes hwf hin hout ready hc obs.frame
  · exact obs.privateFrame s hf (by simp only [slot0_id]; omega)
  · rw [obs.flag]
    exact normalized_zero (wordStep1 bytes).1
  · exact obs.root.2.trans (limbBytes_payload _)

theorem sqrtInput_numerator_bytes (dg : Globals) (s : GlobalState)
    (input : Pointer) (bytes : BitVec 256) (hwf : s.WF) (hin : ReadBytes s input 32 bytes) :
    ReadBytes (sqrtInputState dg s input) (slot3 s) 40 (limbBytes (numeratorWord bytes).limbs) := by
  have hl := sqrtInput_live dg s input _ _ (slot3_live s hwf)
  refine ⟨hl,?_⟩
  change (sqrtInputState dg s input).mem.readAt (slot3 s) 320 =
    fieldPayload (numeratorWord bytes).limbs
  rw [← payload_readLimbs _ _ hl,sqrtInput_numerator dg s input bytes hwf hin]

theorem sqrtInput_denominator_bytes (dg : Globals) (sg : SqrtRatio.Globals) (s : GlobalState)
    (input : Pointer) (bytes : BitVec 256) (hwf : s.WF) (hin : ReadBytes s input 32 bytes)
    (ready : Ready dg sg s) :
    ReadBytes (sqrtInputState dg s input) (slot2 s) 40 (limbBytes (denominatorWord bytes).limbs) := by
  have hl := sqrtInput_live dg s input _ _ (slot2_live s hwf)
  refine ⟨hl,?_⟩
  change (sqrtInputState dg s input).mem.readAt (slot2 s) 320 =
    fieldPayload (denominatorWord bytes).limbs
  rw [← payload_readLimbs _ _ hl,sqrtInput_denominator dg sg s input bytes hwf hin ready]

theorem prefixBoundary_of_provider (dg : Globals) (sg : SqrtRatio.Globals)
    (hprefix : PrefixProvider sg) (s : GlobalState) (out input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : ReadBytes s input 32 bytes) (hout : SmallRange s.mem out 168)
    (ready : Ready dg sg s) : Semantic.PrefixBoundary dg sg out input s bytes := by
  apply prefixBoundary_of_witness dg sg s out input bytes hwf hin hout ready
  unfold wordStep1
  exact hprefix (slot0 s) (slot3 s) (slot2 s) (sqrtInputState dg s input)
    (numeratorWord bytes) (denominatorWord bytes)
    (sqrtInput_frame dg s input hwf).wellFormed
    (sqrtInput_live dg s input _ _ (slot0_live s hwf))
    (sqrtInput_numerator_bytes dg s input bytes hwf hin)
    (sqrtInput_denominator_bytes dg sg s input bytes hwf hin ready)
    (sqrtInput_ready dg sg s input hwf ready).sqrtM1

/-- Only the explicitly specified original sqrt finite prefix remains assumed. -/
theorem contractUnder_of_provider (dg : Globals) (sg : SqrtRatio.Globals)
    (cofactor : Verifier.Execution.ValidPoint → Verifier.Execution.ValidPoint)
    (hprefix : PrefixProvider sg) :
    Verifier.Execution.Dalek.DecompressContractUnder (Ready dg sg) (linkedProgram dg sg).call
      (Verifier.Execution.ValidPoint.layout cofactor)
      (Verifier.Execution.ValidPoint.shared Valid.decode) := by
  apply Semantic.contractUnder_of_prefixes dg sg (Ready dg sg) cofactor
  intro out input s bytes hwf ready hout hin _hd
  exact prefixBoundary_of_provider dg sg hprefix s out input bytes hwf hin hout ready

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge

import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixPointReadback

/-! The whole decoder finite-prefix boundary now reduces solely to the one
concrete sqrt_ratio_i invocation: its returned state, ordinary output frame,
private caller frame, zero/nonzero flag, and exact root words. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
open Verifier.Execution.Dalek (OutputFrame ReadBytes)
open Semantic (PrefixBoundary PrefixPublic SuccessWords)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
attribute [local irreducible] wordStep1 machine

theorem limbs_of_fieldPayload (s : GlobalState) (p : Pointer) (x : Words)
    (hp : SmallRange s.mem p 40) (hx : s.mem.readAt p 320 = fieldPayload x) :
    readLimbs s p = x :=
  readLimbs_of_limbBytes s p x hp hx

/-- This is a single reached call, with its two field inputs already derived by
`sqrt_callsite`. It assumes no decoder execution, prefix, or final contract. -/
theorem prefixBoundary_of_sqrt (g : Globals) (sg : SqrtRatio.Globals)
    (s t : GlobalState) (out input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : ReadBytes s input 32 bytes) (hout : SmallRange s.mem out 168)
    (ready : Ready g sg s)
    (hcall : (decodePrimitives sg).sqrtRatio
      (.cons (.value (slot0 s)) (.cons (.value (slot3 s)) (.cons (.value (slot2 s)) .nil)))
      (sqrtInputState g s input) = .value (.nil,t))
    (frame : OutputFrame (sqrtInputState g s input) t (slot0 s) 48)
    (callerFrame : PrivateFrame s t)
    (hflag : (t.mem.readAt (slot0 s) 8 = 0#8 ↔ (wordStep1 bytes).1 = false))
    (hroot : t.mem.readAt ((slot0 s).add 8#64) 320 =
      fieldPayload (wordStep1 bytes).2.limbs) :
    PrefixBoundary g sg out input s bytes := by
  have entry := outerEntry_of_sqrt g sg s t out input hwf hin.1 hout ready hcall frame
  have hpublic := copies_frame s t callerFrame
  have hlive {q : Pointer} {n : Nat} (h : SmallRange (allocated s).mem q n) :
      SmallRange t.mem q n := frame.live q n (sqrtInput_live g s input q n h)
  have h6 := copies_live s t _ _ (hlive (slot6_live s hwf))
  have h8 := copies_live s t _ _ (hlive (slot8_live s hwf))
  have h9 := copies_live s t _ _ (hlive (slot9_live s hwf))
  refine ⟨copiedPairEnv g s t out input,copiedXYState s t,t.mem.readAt (slot0 s) 8,
    entry.1,entry.2,hflag,?_⟩
  split
  · exact ⟨hpublic.memory,hpublic.counter⟩
  · have hin' : ReadBytes (copiedXYState s t) input 32 bytes :=
      ⟨private_live hpublic hwf hin.1,
        (private_read hpublic input 256 (hwf.lt hin.1.fits.mem)).trans hin.2⟩
    have hroot' : readLimbs (copiedXYState s t) (slot9 s) = (wordStep1 bytes).2.limbs :=
      limbs_of_fieldPayload _ _ _ h9
        ((copied_x_readback s t (hlive (slot7_live s hwf)) (hlive (slot9_live s hwf))).trans hroot)
    have hd50 : (slot5 s).id ≠ (slot0 s).id := by
      intro h
      have := congrArg BlockId.id h
      simp only [slot5_id,slot0_id] at this
      omega
    have hyt : t.mem.readAt (slot5 s) 320 = fieldPayload (parsedWord bytes).limbs := by
      exact (frame.read (slot5 s) 320
        (Or.inl hd50)).trans
        (sqrtInput_parsed320 g s input bytes hwf hin)
    have hy' : readLimbs (copiedXYState s t) (slot8 s) = (parsedWord bytes).limbs :=
      limbs_of_fieldPayload _ _ _ h8
        ((copied_y_readback s t (hlive (slot7_live s hwf)) (hlive (slot8_live s hwf))).trans hyt)
    have hwords := success_words s (copiedXYState s t) input bytes (wordStep1 bytes).2
      hin' h6 h8 h9 hroot' hy'
    have hpublic' := success_prefix_frame s (copiedXYState s t) input hpublic
    refine ⟨successPrefixEnv g s t (copiedXYState s t) out input,
      successPrefixState s (copiedXYState s t) input,⟨slot6 s,slot8 s⟩,
      success_prefix_segment g sg s t (copiedXYState s t) out input hpublic.wellFormed
        hin'.1 h6 h8 h9,
      success_prefix_ready g s t (copiedXYState s t) out input hwf hout hpublic h6 h8,
      ⟨hpublic'.memory,hpublic'.counter⟩,?_,⟨hwords.1,hwords.2.1,hwords.2.2⟩⟩
    simp only [slot6_id]
    omega

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix

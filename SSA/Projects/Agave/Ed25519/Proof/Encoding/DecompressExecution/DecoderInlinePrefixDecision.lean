import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixCopies

/-! Exact outer decision boundary, isolating only the actual sqrt invocation.
This is conditional on that single call's return/frame, never universal
readiness of arbitrary environments. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
open Verifier.Execution.Dalek (OutputFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

theorem copies_live (s t : GlobalState) (q : Pointer) (n : Nat)
    (h : SmallRange t.mem q n) : SmallRange (copiedXYState s t).mem q n :=
  (((h.storeAt _ _).storeAt _ _).storeAt _ _).storeAt _ _

theorem copies_frame (s t : GlobalState) (frame : PrivateFrame s t) :
    PrivateFrame s (copiedXYState s t) := by
  exact ((((frame.storeAt _ _ (by simp only [slot7_id]; omega)).storeAt _ _
    (by simp only [Pointer.add_id, slot7_id]; omega)).storeAt _ _
    (by simp only [slot9_id]; omega)).storeAt _ _ (by simp only [slot8_id]; omega))

theorem copied_decision_ready (g : Globals) (s t : GlobalState) (out input : Pointer)
    (hout : SmallRange t.mem out 168) :
    OuterDecisionReady (copiedPairEnv g s t out input) (copiedXYState s t)
      out (t.mem.readAt (slot0 s) 8) :=
  ⟨rfl, rfl, rfl, rfl, copies_live s t out 168 hout⟩

theorem sqrt_invocation_segment (g : Globals) (sg : SqrtRatio.Globals)
    (s t : GlobalState) (out input : Pointer)
    (hcall : (decodePrimitives sg).sqrtRatio
      (.cons (.value (slot0 s)) (.cons (.value (slot3 s)) (.cons (.value (slot2 s)) .nil)))
      (sqrtInputState g s input) = .value (.nil, t)) :
    Cutpoint.segment (program (decodePrimitives sg) g) 0 121 1
      (sqrtInputEnv g s out input) (sqrtInputState g s input) =
      .value (sqrtInputEnv g s out input, t) := by
  have e30 : (sqrtInputEnv g s out input).read (%30) = .value (slot0 s) := rfl
  have e33 : (sqrtInputEnv g s out input).read (%33) = .value (slot3 s) := rfl
  have e32 : (sqrtInputEnv g s out input).read (%32) = .value (slot2 s) := rfl
  change List.foldlM Instr.run (sqrtInputEnv g s out input)
    [.call (decodePrimitives sg).sqrtRatio (.cons (%30) (.cons (%33) (.cons (%32) .nil))) .nil]
      (sqrtInputState g s input) = _
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, Regs.read_cons,
    Regs.read_nil,e30,e33,e32, EffectM.bind_eq,EffectM.pure_eq,hcall,
    PoisonOr.value_bind,Env.writeMany_nil]

/-- A concrete sqrt call and its ordinary output frame suffice for the entire
bb0 prefix to reach the exact decision readiness; no later arithmetic is assumed. -/
theorem outerEntry_of_sqrt (g : Globals) (sg : SqrtRatio.Globals)
    (s t : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hin : SmallRange s.mem input 32) (hout : SmallRange s.mem out 168)
    (ready : Ready g sg s)
    (hcall : (decodePrimitives sg).sqrtRatio
      (.cons (.value (slot0 s)) (.cons (.value (slot3 s)) (.cons (.value (slot2 s)) .nil)))
      (sqrtInputState g s input) = .value (.nil, t))
    (frame : OutputFrame (sqrtInputState g s input) t (slot0 s) 48) :
    outerEntryPrefix (decodePrimitives sg) g (initialEnv out input) s =
        .value (copiedPairEnv g s t out input, copiedXYState s t) ∧
      OuterDecisionReady (copiedPairEnv g s t out input) (copiedXYState s t)
        out (t.mem.readAt (slot0 s) 8) := by
  constructor
  · unfold outerEntryPrefix
    rw [show 137 = 121 + 16 from rfl, segment_append]
    simp only [Nat.reduceAdd, EffectM.bind_eq,
      through_denominator_segment g sg s out input hwf hin ready, PoisonOr.value_bind]
    rw [show 16 = 1 + 15 from rfl, segment_append]
    simp only [Nat.reduceAdd, EffectM.bind_eq,
      sqrt_invocation_segment g sg s t out input hcall, PoisonOr.value_bind]
    exact copies_segment (decodePrimitives sg) g s t out input
      (frame.live _ _ (sqrtInput_live g s input _ _ (slot0_live s hwf)))
      (frame.live _ _ (sqrtInput_live g s input _ _ (slot5_live s hwf)))
      (frame.live _ _ (sqrtInput_live g s input _ _ (slot7_live s hwf)))
      (frame.live _ _ (sqrtInput_live g s input _ _ (slot8_live s hwf)))
      (frame.live _ _ (sqrtInput_live g s input _ _ (slot9_live s hwf)))
  · exact copied_decision_ready g s t out input
      (frame.live _ _ (private_live (sqrtInput_frame g s input hwf) hwf hout))

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix

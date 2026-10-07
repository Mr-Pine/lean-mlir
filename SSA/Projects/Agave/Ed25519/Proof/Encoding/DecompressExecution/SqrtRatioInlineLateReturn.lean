import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineLateExecution

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate
open LeanMLIR.RIR SerialFieldMul Inline
open Reduce64.Execution (SmallRange)
open Inline956 (byte)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes SerialFieldMul.machine

/-- The original continuation returns after storing the specified root and flag. -/
theorem resume (g : Globals) (E0 E : Env program.Γ) (s t : GlobalState)
    (out : Pointer) (a b : Pow22501.TightWords) (hwf : s.WF)
    (ho : SmallRange s.mem out 48) (hg : SmallRange s.mem g.address0 40)
    (hgi : readLimbs s g.address0 = sqrtM1Word.limbs)
    (hout : E0.read (%arg0) = .value out) (h : At577 g E0 E s t a b) :
    Cutpoint.resume (program sqrtRatioPrimitives g) 0 577 E t =
      .value (.nil,outputState (state1047 g s t a b) out
        (byte (wordSqrt a b).1) (limbBytes (wordSqrt a b).2.limbs)) := by
  obtain ⟨F,d,hsegment,hready,hroot,hflag,_⟩ := segment g E0 E s t out a b hwf ho hg hgi hout h
  rw [Cutpoint.after_segment (program sqrtRatioPrimitives g) 0 577 470 E F t
    (state1047 g s t a b) hsegment]
  rw [output_run g F (state1047 g s t a b) out d.root d.first d.second
    hready.wf hready.outputLive hready.rootLive hready.disjoint
    hready.outputRegister hready.rootRegister hready.firstRegister hready.secondRegister
    hready.eightRegister hready.fortyRegister,hroot,hflag]

/-- The stored limb model denotes the mathematical square-root-ratio result. -/
theorem root_value (g : Globals) (s t : GlobalState) (a b : Pow22501.TightWords)
    (h : ScratchFrame s t) :
    wordValue (readLimbs (state1047 g s t a b) (slot s 17)) =
      (Decompress.sqrtRatio (wordValue a.limbs) (wordValue b.limbs)).2 := by
  have hx := readLimbs_of_limbBytes (state1047 g s t a b) (slot s 17)
    (wordSqrt a b).2.limbs ((state1047_scratch g s t a b h).slots 17)
    (state1047_root g s t a b h)
  rw [hx]
  exact congrArg Prod.snd (wordSqrt_value a b)

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate

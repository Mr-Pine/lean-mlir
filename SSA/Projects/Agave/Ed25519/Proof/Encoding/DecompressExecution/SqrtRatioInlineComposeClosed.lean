import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeProduct
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeGlobals
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposePieces
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineLateExecution
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioCallFromPrefix

/-! All original instructions before the output cutpoint, including every real
helper call, follow from well-formed memory, live inputs and the emitted sqrt(-1)
bytes. No execution result or algebraic output is assumed. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open Verifier.Execution.Dalek (ReadBytes)
open Pow22501 (TightWords)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] wordSqrt

theorem prefix1047 (g : Globals) (E : Env program.Γ) (s : GlobalState)
    (out u v : Pointer) (a b : TightWords) (hwf : s.WF)
    (ho : SmallRange s.mem out 48)
    (hu : ReadBytes s u 40 (limbBytes a.limbs))
    (hv : ReadBytes s v 40 (limbBytes b.limbs))
    (hg : ReadBytes s g.address0 40 sqrtM1.bytes)
    (heo : E.read (%arg0) = .value out)
    (heu : E.read (%arg1) = .value u) (hev : E.read (%arg2) = .value v) :
    ∃ (F : Env program.Γ) (z : GlobalState) (d : ExecutionOutputData),
      Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 1047 E s = .value (F,z) ∧
      ExecutionOutputReady F z out d ∧ ScratchFrame s z ∧
      z.mem.readAt d.root 320 = limbBytes (wordSqrt a b).2.limbs ∧
      d.first ||| d.second = if (wordSqrt a b).1 then 1#8 else 0#8 := by
  have hua := readLimbs_of_limbBytes s u a.limbs hu.1 hu.2
  have hvb := readLimbs_of_limbBytes s v b.limbs hv.1 hv.2
  have hgi := sqrtM1_words s g.address0 hg
  obtain ⟨F,hprefix,hcommon,hsecond⟩ := prefix577 g E s u v hwf hu.1 hv.1 hg.1 heu hev
  have hw := state577_candidate_check g s u v a b hwf hua hvb
  have hat : InlineLate.At577 g E F s (state577 g s u v) a b := by
    refine ⟨state577_scratch g s u v hwf,hcommon.base,hcommon.p85,hcommon.p87,
      hcommon.p89,hcommon.p91,?_,?_,hw.2,hw.1,
      state577_product g s u v a hwf hu.1 hg.1 hua hgi⟩
    · simpa only [firstByte_semantic s u v a b hwf hu.1 hua hvb,Inline956.byte]
        using hcommon.first
    · simpa only [secondByte_semantic s u v a b hwf hu.1 hua hvb,Inline956.byte]
        using hsecond
  obtain ⟨G,z,d,hlate,hready,hroot,hflag,hframe⟩ :=
    InlineLate.reaches_output g E F s (state577 g s u v) out a b hwf ho hg.1 hgi heo hat
  refine ⟨G,z,d,?_,hready,hframe,hroot,hflag⟩
  rw [show 1047 = 577 + 470 from rfl,segment_append]
  simp only [EffectM.bind_eq,hprefix,PoisonOr.value_bind]
  exact hlate

/-- The previously named piecewise execution prefix has no residual execution premise. -/
theorem executionPrefix_of_ready (g : Globals) (E : Env program.Γ) (s : GlobalState)
    (out u v : Pointer) (a b : TightWords) (hwf : s.WF)
    (ho : SmallRange s.mem out 48)
    (hu : ReadBytes s u 40 (limbBytes a.limbs))
    (hv : ReadBytes s v 40 (limbBytes b.limbs))
    (hg : ReadBytes s g.address0 40 sqrtM1.bytes)
    (heo : E.read (%arg0) = .value out)
    (heu : E.read (%arg1) = .value u) (hev : E.read (%arg2) = .value v) :
    ∃ (F : Env program.Γ) (z : GlobalState) (d : ExecutionOutputData),
      executionPrefix g E s = .value (F,z) ∧
      ExecutionOutputReady F z out d ∧ ScratchFrame s z ∧
      z.mem.readAt d.root 320 = limbBytes (wordSqrt a b).2.limbs ∧
      d.first ||| d.second = if (wordSqrt a b).1 then 1#8 else 0#8 := by
  rw [executionPrefix_eq_segment]
  exact prefix1047 g E s out u v a b hwf ho hu hv hg heo heu hev

theorem prefixWitness_of_ready (g : Globals) (out u v : Pointer) (s : GlobalState)
    (a b : TightWords) (hwf : s.WF) (ho : SmallRange s.mem out 48)
    (hu : ReadBytes s u 40 (limbBytes a.limbs))
    (hv : ReadBytes s v 40 (limbBytes b.limbs))
    (hg : ReadBytes s g.address0 40 sqrtM1.bytes) :
    CallFromPrefix.PrefixWitness g out u v s (wordSqrt a b) :=
  prefix1047 g (Env.init (program.args (.value out) (.value u) (.value v)).get)
    s out u v a b hwf ho hu hv hg rfl rfl rfl

/-- The complete linked helper call computes the mathematical word model and
preserves every unrelated caller allocation. -/
theorem call_of_ready (g : Globals) (out u v : Pointer) (s : GlobalState)
    (a b : TightWords) (hwf : s.WF) (ho : SmallRange s.mem out 48)
    (hu : ReadBytes s u 40 (limbBytes a.limbs))
    (hv : ReadBytes s v 40 (limbBytes b.limbs))
    (hg : ReadBytes s g.address0 40 sqrtM1.bytes) :
    ∃ after, (program sqrtRatioPrimitives g).call
      (program.args (.value out) (.value u) (.value v)) s = .value (.nil,after) ∧
      CallFromPrefix.CallObservation s after out (wordSqrt a b) :=
  CallFromPrefix.call_of_witness g out u v s (wordSqrt a b) hwf ho
    (prefixWitness_of_ready g out u v s a b hwf ho hu hv hg)

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline

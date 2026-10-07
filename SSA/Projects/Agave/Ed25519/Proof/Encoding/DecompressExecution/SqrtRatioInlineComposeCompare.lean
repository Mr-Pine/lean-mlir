import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeFirst
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioHelperFrames

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open Pow22501 (TightWords)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes machine

theorem cached_frame (E F : Env program.Γ) (h : SerializerFrame.Frame 236 E F)
    (hc : Inline308.Cached E bytes) : Inline308.Cached F bytes := by
  intro i
  have hb := hc i
  fin_cases i <;> exact (h.2 _ (by decide)).trans hb

def firstByte (s : GlobalState) (u v : Pointer) : BitVec 8 :=
  Helpers.comparison (Helpers.serialize (state306 s u v) (slot s 4) u) (slot s 5) (slot s 4)

def state308 (s : GlobalState) (u v : Pointer) : GlobalState :=
  Helpers.advance (Helpers.serialize (state306 s u v) (slot s 4) u) 33

theorem state308_scratch (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    ScratchFrame s (state308 s u v) :=
  ((state306_scratch s u v hwf).storeBytes (slot s 4) _ (slot_private s 4)).advance 33

theorem firstByte_semantic (s : GlobalState) (u v : Pointer) (a b : TightWords)
    (hwf : s.WF) (hu : SmallRange s.mem u 40)
    (hua : readLimbs s u = a.limbs) (hvb : readLimbs s v = b.limbs) :
    firstByte s u v = if equalWords (wordCheck a b) a then 1#8 else 0#8 := by
  have hs := state117_scratch s u v hwf
  have hc := (state117_words s u v a b hwf hua hvb).2
  apply Helpers.comparison_equalWords _ _ _ (wordCheck a b) a
  · rw [Helpers.serialize_read_other _ (slot s 4) u (slot s 5) 256
      (slot_distinct s 4 5 (by decide))]
    change (Inline117.resultState (state117 s u v) (slot s 5) _).mem.readAt _ _ = _
    rw [Inline117.result_word _ (slot s 5) _ (hs.slots 5),hc]
  · rw [Helpers.serialize_read _ (slot s 4) u ((state306_scratch s u v hwf).slots 4),
      (state306_scratch s u v hwf).old_words hwf hu,hua]

theorem prefix308 (g : Globals) (E : Env program.Γ) (s : GlobalState) (u v : Pointer)
    (hwf : s.WF) (hu : SmallRange s.mem u 40) (hv : SmallRange s.mem v 40)
    (heu : E.read (%arg1) = .value u) (hev : E.read (%arg2) = .value v) :
    ∃ F : Env program.Γ, Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 308 E s =
        .value (F,state308 s u v) ∧
      SerializerFrame.Frame 84 (entryResult g E s).1 F ∧
      Inline308.Cached F (ToBytes.machine (readLimbs (state117 s u v) (slot s 13))) ∧
      F.read (%85) = .value ((slot s 13).add 8#64) ∧
      F.read (%87) = .value ((slot s 13).add 16#64) ∧
      F.read (%89) = .value ((slot s 13).add 24#64) ∧
      F.read (%91) = .value ((slot s 13).add 32#64) ∧
      F.read (%236) = .value (firstByte s u v) := by
  obtain ⟨F,hprefix,hframe,hcached,h85,h87,h89,h91⟩ := prefix306 g E s u v hwf hu hv heu hev
  have hs := state306_scratch s u v hwf
  have hslots (i : Fin 22) : F.read (slotRegister i) = .value (slot s i) :=
    (frame_slot _ F hframe i).trans (entry_slot g E s i)
  have hfarg : F.read (%arg1) = .value u := by
    change F.args 1 = .value u
    rw [hframe.1,entry_args]
    exact heu
  have hc := Helpers.segment_306_308 g F (state306 s u v) (slot s 4) u (slot s 5)
    hs.wf (hs.slots 4) (hs.old_live hwf hu) (hs.slots 5) (hslots 4) hfarg (hslots 5)
  let G : Env program.Γ := F[%236 := .value (firstByte s u v)]
  have hg : SerializerFrame.Frame 236 F G := SerializerFrame.Frame.write F _ _ (by decide)
  refine ⟨G,?_,hframe.trans (hg.mono (by decide)),cached_frame F G hg hcached,?_,?_,?_,?_,?_⟩
  · rw [show 308 = 306 + 2 from rfl,segment_append]
    simp only [EffectM.bind_eq,hprefix,PoisonOr.value_bind]
    exact hc
  · exact (hg.2 85 (by decide)).trans h85
  · exact (hg.2 87 (by decide)).trans h87
  · exact (hg.2 89 (by decide)).trans h89
  · exact (hg.2 91 (by decide)).trans h91
  · simp only [G,mlir_env]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline

import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeCompare
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Readback

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open Pow22501 (TightWords)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes machine negativeWords

structure CommonRegisters (g : Globals) (E0 : Env program.Γ) (s : GlobalState)
    (u v : Pointer) (E : Env program.Γ) : Prop where
  base : SerializerFrame.Frame 84 (entryResult g E0 s).1 E
  p85 : E.read (%85) = .value ((slot s 13).add 8#64)
  p87 : E.read (%87) = .value ((slot s 13).add 16#64)
  p89 : E.read (%89) = .value ((slot s 13).add 24#64)
  p91 : E.read (%91) = .value ((slot s 13).add 32#64)
  first : E.read (%236) = .value (firstByte s u v)

theorem CommonRegisters.frame (h : CommonRegisters g E0 s u v E)
    (hf : SerializerFrame.Frame 237 E F) : CommonRegisters g E0 s u v F :=
  ⟨h.base.trans (hf.mono (by decide)),(hf.2 85 (by decide)).trans h.p85,
    (hf.2 87 (by decide)).trans h.p87,(hf.2 89 (by decide)).trans h.p89,
    (hf.2 91 (by decide)).trans h.p91,(hf.2 236 (by decide)).trans h.first⟩

def state569 (s : GlobalState) (u v : Pointer) : GlobalState :=
  Inline308.resultState (state308 s u v) u (slot s 3) (slot s 2)
    (ToBytes.machine (readLimbs (state117 s u v) (slot s 13)))

def secondByte (s : GlobalState) (u v : Pointer) : BitVec 8 :=
  Helpers.comparison (state569 s u v) (slot s 3) (slot s 2)

theorem state569_scratch (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    ScratchFrame s (state569 s u v) :=
  ((state308_scratch s u v hwf).storeBytes (slot s 3) _ (slot_private s 3)).storeBytes
    (slot s 2) _ (slot_private s 2)

theorem secondByte_semantic (s : GlobalState) (u v : Pointer) (a b : TightWords)
    (hwf : s.WF) (hu : SmallRange s.mem u 40)
    (hua : readLimbs s u = a.limbs) (hvb : readLimbs s v = b.limbs) :
    secondByte s u v = if equalWords (wordCheck a b) (negativeWord a) then 1#8 else 0#8 := by
  have hs := state308_scratch s u v hwf
  apply Helpers.comparison_equalWords _ _ _ (wordCheck a b) (negativeWord a)
  · change (Inline308.resultState _ u (slot s 3) (slot s 2) _).mem.readAt _ _ = _
    rw [Inline308.result_left _ u (slot s 3) (slot s 2) _ (hs.slots 3)
      (slot_distinct s 2 3 (by decide)),(state117_words s u v a b hwf hua hvb).2]
  · change (Inline308.resultState _ u (slot s 3) (slot s 2) _).mem.readAt _ _ = _
    rw [Inline308.result_right _ u (slot s 3) (slot s 2) _ (hs.slots 2),
      hs.old_words hwf hu,hua]
    rfl

theorem state308_words (s : GlobalState) (u v p : Pointer)
    (h4 : (slot s 4).id ≠ p.id) (h5 : (slot s 5).id ≠ p.id) :
    readLimbs (state308 s u v) p = readLimbs (state117 s u v) p := by
  funext i
  exact (Helpers.serialize_read_other (state306 s u v) (slot s 4) u (p.add _) 64 h4).trans
    (Inline117.result_read (state117 s u v) (slot s 5) (p.add _) _ h5 64)

theorem state569_words (s : GlobalState) (u v p : Pointer)
    (h2 : (slot s 2).id ≠ p.id) (h3 : (slot s 3).id ≠ p.id)
    (h4 : (slot s 4).id ≠ p.id) (h5 : (slot s 5).id ≠ p.id) :
    readLimbs (state569 s u v) p = readLimbs (state117 s u v) p := by
  funext i
  exact (Inline308.result_read_ne (state308 s u v) u (slot s 3) (slot s 2)
    (p.add _) _ h3 h2 64).trans (congrArg (fun x : Words => x i) (state308_words s u v p h4 h5))

theorem prefix569 (g : Globals) (E : Env program.Γ) (s : GlobalState) (u v : Pointer)
    (hwf : s.WF) (hu : SmallRange s.mem u 40) (hv : SmallRange s.mem v 40)
    (heu : E.read (%arg1) = .value u) (hev : E.read (%arg2) = .value v) :
    ∃ F : Env program.Γ, Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 569 E s =
        .value (F,state569 s u v) ∧ CommonRegisters g E s u v F ∧
      F.read (%300) = .value ((slot s 10).add 8#64) ∧
      F.read (%312) = .value (negativeWords (readLimbs (state308 s u v) u) 0) ∧
      F.read (%313) = Ty.wrap #v[negativeWords (readLimbs (state308 s u v) u) 1,
        negativeWords (readLimbs (state308 s u v) u) 2,
        negativeWords (readLimbs (state308 s u v) u) 3,
        negativeWords (readLimbs (state308 s u v) u) 4] := by
  obtain ⟨F,hprefix,hframe,hcached,h85,h87,h89,h91,hfirst⟩ := prefix308 g E s u v hwf hu hv heu hev
  have hs := state308_scratch s u v hwf
  have hslots (i : Fin 22) : F.read (slotRegister i) = .value (slot s i) :=
    (frame_slot _ F hframe i).trans (entry_slot g E s i)
  have hfarg : F.read (%arg1) = .value u := by
    change F.args 1 = .value u
    rw [hframe.1,entry_args]
    exact heu
  have hc := Inline308.segment sqrtRatioPrimitives g F (state308 s u v) u
    (slot s 3) (slot s 2) (slot s 10) _ (hs.old_live hwf hu) (hs.slots 3)
    (hs.slots 2) (hs.slots 10) (frame_constants _ F hframe (entry_constants g E s))
    hcached hfarg (hslots 3) (hslots 2) (hslots 10) (slot_caller_disjoint s hwf 3 u hu)
  let G : Env program.Γ := Inline308.resultEnv F u (slot s 3) (slot s 2) (slot s 10) (readLimbs (state308 s u v) u)
  have hg : SerializerFrame.Frame 237 F G := Inline308.result_frame _ _ _ _ _ _
  refine ⟨G,?_,CommonRegisters.frame ⟨hframe,h85,h87,h89,h91,hfirst⟩ hg,
    Inline308.result_negative_ptr _ _ _ _ _ _,Inline308.result_negative_low _ _ _ _ _ _,
    Inline308.result_negative_high _ _ _ _ _ _⟩
  rw [show 569 = 308 + 261 from rfl,segment_append]
  simp only [EffectM.bind_eq,hprefix,PoisonOr.value_bind]
  exact hc

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline

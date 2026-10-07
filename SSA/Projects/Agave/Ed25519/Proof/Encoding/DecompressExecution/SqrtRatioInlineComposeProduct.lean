import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeSecond

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open Pow22501 (TightWords)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes machine negativeWords

def state576 (s : GlobalState) (u v : Pointer) : GlobalState :=
  Helpers.negativeState (Helpers.advance (state569 s u v) 33) (slot s 10)
    (negativeWords (readLimbs (state308 s u v) u))

def state577 (g : Globals) (s : GlobalState) (u v : Pointer) : GlobalState :=
  Helpers.multiply (state576 s u v) (slot s 11) (slot s 10) g.address0

theorem state576_scratch (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    ScratchFrame s (state576 s u v) := by
  exact (((state569_scratch s u v hwf).advance 33).storeAt (slot s 10) _ (slot_private s 10)).storeAt
    ((slot s 10).add 8) _ (slot_private s 10)

theorem state577_scratch (g : Globals) (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    ScratchFrame s (state577 g s u v) :=
  (state576_scratch s u v hwf).storeLimbs (slot s 11) _ (slot_private s 11)

theorem state576_negative (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    readLimbs (state576 s u v) (slot s 10) = negativeWords (readLimbs (state308 s u v) u) :=
  Helpers.negativeState_readLimbs _ (slot s 10) _ ((state569_scratch s u v hwf).slots 10)

theorem state577_product (g : Globals) (s : GlobalState) (u v : Pointer) (a : TightWords)
    (hwf : s.WF) (hu : SmallRange s.mem u 40) (hg : SmallRange s.mem g.address0 40)
    (hua : readLimbs s u = a.limbs) (hgs : readLimbs s g.address0 = sqrtM1Word.limbs) :
    readLimbs (state577 g s u v) (slot s 11) = ((negativeWord a).mul sqrtM1Word).limbs := by
  change readLimbs (Helpers.multiply (state576 s u v) (slot s 11) (slot s 10) g.address0) _ = _
  rw [Helpers.multiply_readLimbs _ (slot s 11) (slot s 10) g.address0
      ((state576_scratch s u v hwf).slots 11),state576_negative s u v hwf,
      (state308_scratch s u v hwf).old_words hwf hu,hua,
      (state576_scratch s u v hwf).old_words hwf hg,hgs]
  rfl

theorem state577_words (g : Globals) (s : GlobalState) (u v p : Pointer)
    (h2 : (slot s 2).id ≠ p.id) (h3 : (slot s 3).id ≠ p.id)
    (h4 : (slot s 4).id ≠ p.id) (h5 : (slot s 5).id ≠ p.id)
    (h10 : (slot s 10).id ≠ p.id) (h11 : (slot s 11).id ≠ p.id) :
    readLimbs (state577 g s u v) p = readLimbs (state117 s u v) p := by
  funext i
  exact (Helpers.multiply_read_other (state576 s u v) (slot s 11) (slot s 10) g.address0
    (p.add _) 64 h11).trans ((Helpers.negativeState_read_other
      (Helpers.advance (state569 s u v) 33) (slot s 10) (p.add _) _ 64 h10).trans
        (congrArg (fun x : Words => x i) (state569_words s u v p h2 h3 h4 h5)))

theorem state577_candidate_check (g : Globals) (s : GlobalState) (u v : Pointer) (a b : TightWords)
    (hwf : s.WF) (hua : readLimbs s u = a.limbs) (hvb : readLimbs s v = b.limbs) :
    readLimbs (state577 g s u v) (slot s 17) = (wordCandidate a b).limbs ∧
    readLimbs (state577 g s u v) (slot s 13) = (wordCheck a b).limbs := by
  have h := state117_words s u v a b hwf hua hvb
  constructor
  · exact (state577_words g s u v (slot s 17) (slot_distinct s 2 17 (by decide))
      (slot_distinct s 3 17 (by decide)) (slot_distinct s 4 17 (by decide))
      (slot_distinct s 5 17 (by decide)) (slot_distinct s 10 17 (by decide))
      (slot_distinct s 11 17 (by decide))).trans h.1
  · exact (state577_words g s u v (slot s 13) (slot_distinct s 2 13 (by decide))
      (slot_distinct s 3 13 (by decide)) (slot_distinct s 4 13 (by decide))
      (slot_distinct s 5 13 (by decide)) (slot_distinct s 10 13 (by decide))
      (slot_distinct s 11 13 (by decide))).trans h.2

theorem prefix577 (g : Globals) (E : Env program.Γ) (s : GlobalState) (u v : Pointer)
    (hwf : s.WF) (hu : SmallRange s.mem u 40) (hv : SmallRange s.mem v 40)
    (hg : SmallRange s.mem g.address0 40)
    (heu : E.read (%arg1) = .value u) (hev : E.read (%arg2) = .value v) :
    ∃ F : Env program.Γ, Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 577 E s =
        .value (F,state577 g s u v) ∧ CommonRegisters g E s u v F ∧
      F.read (%430) = .value (secondByte s u v) := by
  obtain ⟨F,hprefix,hcommon,hptr,hlow,hhigh⟩ := prefix569 g E s u v hwf hu hv heu hev
  have hs := state569_scratch s u v hwf
  have hslots (i : Fin 22) : F.read (slotRegister i) = .value (slot s i) :=
    (frame_slot _ F hcommon.base i).trans (entry_slot g E s i)
  have h52 : F.read (%52) = .value g.address0 :=
    (hcommon.base.2 52 (by decide)).trans (entry_sqrtM1 g E s)
  have hc := Helpers.segment_569_577 g F (state569 s u v) (slot s 3) (slot s 2)
    (slot s 10) (slot s 11) g.address0 (negativeWords (readLimbs (state308 s u v) u))
    hs.wf (hs.slots 3) (hs.slots 2) (hs.slots 10) (hs.slots 11) (hs.old_live hwf hg)
    (hslots 3) (hslots 2) (hslots 10) (by simpa only [BitVec.ofNat_eq_ofNat] using hptr)
    hlow hhigh (hslots 11) h52
  let G : Env program.Γ := F[%430 := .value (secondByte s u v)]
  have hgframe : SerializerFrame.Frame 237 F G := SerializerFrame.Frame.write F _ _ (by decide)
  refine ⟨G,?_,hcommon.frame hgframe,?_⟩
  · rw [show 577 = 569 + 8 from rfl,segment_append]
    simp only [EffectM.bind_eq,hprefix,PoisonOr.value_bind]
    exact hc
  · simp only [G,mlir_env]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline

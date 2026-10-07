import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineComposeFirst
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Execution
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioHelperFrames
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline956Readback

/-! Memory and register facts for the actual late sqrt continuation. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate
open LeanMLIR.RIR SerialFieldMul Inline
open Reduce64.Execution (SmallRange)
open Inline956 (byte)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes SerialFieldMul.machine

/-- The two original inlined serializers, with their actual stack slots. -/
def state947 (s t : GlobalState) : GlobalState :=
  Inline577.resultState t (slot s 13) (slot s 11) (slot s 1) (slot s 0)

def state956 (g : Globals) (s t : GlobalState) : GlobalState :=
  Helpers.advance (Helpers.multiply (Helpers.advance (state947 s t) 33)
    (slot s 9) g.address0 (slot s 17)) 1

def correction (a b : Pow22501.TightWords) : BitVec 8 :=
  byte (equalWords (wordCheck a b) (negativeWord a) ||
    equalWords (wordCheck a b) ((negativeWord a).mul sqrtM1Word))

def state1047 (g : Globals) (s t : GlobalState) (a b : Pow22501.TightWords) : GlobalState :=
  Inline956.tailState (state956 g s t) (slot s 17) (slot s 9) (correction a b)
    (wordCandidate a b).limbs (sqrtM1Word.mul (wordCandidate a b)).limbs

theorem state947_scratch (s t : GlobalState) (h : ScratchFrame s t) :
    ScratchFrame s (state947 s t) :=
  (h.storeBytes (slot s 1) _ (slot_private s 1)).storeBytes
    (slot s 0) _ (slot_private s 0)

theorem state956_scratch (g : Globals) (s t : GlobalState) (h : ScratchFrame s t) :
    ScratchFrame s (state956 g s t) :=
  (((state947_scratch s t h).advance 33).storeLimbs
    (slot s 9) _ (slot_private s 9)).advance 1

theorem state1047_scratch (g : Globals) (s t : GlobalState) (a b : Pow22501.TightWords)
    (h : ScratchFrame s t) : ScratchFrame s (state1047 g s t a b) := by
  let x := Inline956.rootWords (slot s 17) (slot s 9) (correction a b)
    (wordCandidate a b).limbs (sqrtM1Word.mul (wordCandidate a b)).limbs
  exact ((((state956_scratch g s t h).advance 1).storeAt (slot s 17) (x 0)
    (slot_private s 17)).storeAt ((slot s 17).add 8#64) (x 2 ++ x 1)
    (slot_private s 17)).storeAt ((slot s 17).add 24#64) (x 4 ++ x 3)
    (slot_private s 17)

theorem state947_words (s t : GlobalState) (i : Fin 22) (h1 : (1 : Fin 22) ≠ i)
    (h0 : (0 : Fin 22) ≠ i) :
    readLimbs (state947 s t) (slot s i) = readLimbs t (slot s i) :=
  Inline577.result_words t _ _ _ _ _ (slot_distinct s 1 i h1) (slot_distinct s 0 i h0)

theorem state956_candidate (g : Globals) (s t : GlobalState) :
    readLimbs (state956 g s t) (slot s 17) = readLimbs t (slot s 17) := by
  have h : readLimbs (state956 g s t) (slot s 17) =
      readLimbs (state947 s t) (slot s 17) := by
    funext i
    exact Helpers.multiply_read_other (Helpers.advance (state947 s t) 33)
      (slot s 9) g.address0 (slot s 17) ((slot s 17).add _) 64
      (slot_distinct s 9 17 (by decide))
  exact h.trans (state947_words s t 17 (by decide) (by decide))

theorem state956_replacement (g : Globals) (s t : GlobalState) (a b : Pow22501.TightWords)
    (hwf : s.WF) (h : ScratchFrame s t) (hg : SmallRange s.mem g.address0 40)
    (hgi : readLimbs s g.address0 = sqrtM1Word.limbs)
    (hc : readLimbs t (slot s 17) = (wordCandidate a b).limbs) :
    readLimbs (state956 g s t) (slot s 9) =
      (sqrtM1Word.mul (wordCandidate a b)).limbs := by
  have hs := state947_scratch s t h
  change readLimbs (Helpers.multiply (Helpers.advance (state947 s t) 33)
    (slot s 9) g.address0 (slot s 17)) (slot s 9) = _
  rw [Helpers.multiply_readLimbs (Helpers.advance (state947 s t) 33)
    (slot s 9) g.address0 (slot s 17) (hs.slots 9)]
  change machine (readLimbs (state947 s t) g.address0)
    (readLimbs (state947 s t) (slot s 17)) = _
  rw [hs.old_words hwf hg,hgi]
  have hx : readLimbs (state947 s t) (slot s 17) = (wordCandidate a b).limbs :=
    (state947_words s t 17 (by decide) (by decide)).trans hc
  rw [hx]
  rfl

theorem state947_comparison (s t : GlobalState) (a b : Pow22501.TightWords)
    (h : ScratchFrame s t)
    (hc : readLimbs t (slot s 13) = (wordCheck a b).limbs)
    (hn : readLimbs t (slot s 11) = ((negativeWord a).mul sqrtM1Word).limbs) :
    Helpers.comparison (state947 s t) (slot s 1) (slot s 0) =
      byte (equalWords (wordCheck a b) ((negativeWord a).mul sqrtM1Word)) := by
  apply Helpers.comparison_equalWords
  · rw [state947,Inline577.result_first_canonical t (slot s 13) (slot s 11) (slot s 1) (slot s 0) (h.slots 1)
      (slot_distinct s 0 1 (by decide)),hc]
  · rw [state947,Inline577.result_second_canonical t (slot s 13) (slot s 11) (slot s 1) (slot s 0) (h.slots 0)
      (slot_distinct s 1 11 (by decide)),hn]

theorem state1047_root (g : Globals) (s t : GlobalState) (a b : Pow22501.TightWords)
    (h : ScratchFrame s t) :
    (state1047 g s t a b).mem.readAt (slot s 17) 320 = limbBytes (wordSqrt a b).2.limbs := by
  rw [state1047,Inline956.tailState_read (state956 g s t) (slot s 17) (slot s 9)
    (correction a b) (wordCandidate a b).limbs (sqrtM1Word.mul (wordCandidate a b)).limbs
    ((state956_scratch g s t h).slots 17)]
  rw [correction,Inline956.rootWords_sqrt]

/-- Low register facts are inherited from the real entry allocations. -/
theorem frame_slot_value (g : Globals) (E0 E : Env program.Γ) (s : GlobalState)
    (h : SerializerFrame.Frame 84 (entryResult g E0 s).1 E) (i : Fin 22) :
    E.read (slotRegister i) = .value (slot s i) :=
  (frame_slot _ _ h i).trans (entry_slot g E0 s i)

theorem constants577 (g : Globals) (E0 E : Env program.Γ) (s : GlobalState)
    (h : SerializerFrame.Frame 84 (entryResult g E0 s).1 E) : Inline577.Constants E := by
  have hc := frame_constants _ _ h (entry_constants g E0 s)
  exact ⟨hc.c1,hc.c3,hc.c4,hc.c5,hc.c6,hc.c7,hc.c8,hc.c9,hc.c10,hc.c11,hc.c12,hc.c13,hc.c14,hc.c15,hc.c16,hc.c17,hc.c18,hc.c19,hc.c20,hc.c21,hc.c22,hc.c23,hc.c24,hc.c25,hc.c26,hc.c27,hc.c28,hc.c29,hc.c30,hc.c31,hc.c32,hc.c33,hc.c34,hc.c35,hc.c36,hc.c37,hc.c38,hc.c39,hc.c40,hc.c41,hc.c42,hc.c43,hc.c44,hc.c45,hc.c46⟩

theorem correction_frame (E : Env program.Γ) (eq previous : BitVec 8) :
    SerializerFrame.Frame 731 E (Helpers.correctionEnv E eq previous) := by
  have h1 : SerializerFrame.Frame 731 E (E[%731 := .value eq]) :=
    SerializerFrame.Frame.write E (%731) (.value eq) (by decide)
  have h2 : SerializerFrame.Frame 731 (E[%731 := .value eq])
      (E[%731 := .value eq,%732 := .value (eq ||| previous)]) :=
    SerializerFrame.Frame.write (E[%731 := .value eq]) (%732) (.value (eq ||| previous)) (by decide)
  have h3 : SerializerFrame.Frame 731 (E[%731 := .value eq,%732 := .value (eq ||| previous)])
      (Helpers.correctionEnv E eq previous) :=
    SerializerFrame.Frame.write (E[%731 := .value eq,%732 := .value (eq ||| previous)]) (%733) (.value (eq ||| previous)) (by decide)
  exact h1.trans (h2.trans h3)

theorem registers956 (g : Globals) (E0 E : Env program.Γ) (s : GlobalState)
    (h : SerializerFrame.Frame 84 (entryResult g E0 s).1 E) (eq previous : BitVec 8) :
    Inline956.Registers (Helpers.correctionEnv E eq previous) (slot s 17) (slot s 9)
      (eq ||| previous) := by
  have hf := h.trans ((correction_frame E eq previous).mono (by decide))
  constructor
  · exact (hf.2 3 (by decide)).trans (show (entryResult g E0 s).1.read (%3) = _ from rfl)
  · exact (hf.2 5 (by decide)).trans (show (entryResult g E0 s).1.read (%5) = _ from rfl)
  · exact (hf.2 7 (by decide)).trans (show (entryResult g E0 s).1.read (%7) = _ from rfl)
  · exact (hf.2 8 (by decide)).trans (show (entryResult g E0 s).1.read (%8) = _ from rfl)
  · exact (hf.2 9 (by decide)).trans (show (entryResult g E0 s).1.read (%9) = _ from rfl)
  · exact (hf.2 10 (by decide)).trans (show (entryResult g E0 s).1.read (%10) = _ from rfl)
  · exact (hf.2 50 (by decide)).trans (show (entryResult g E0 s).1.read (%50) = _ from rfl)
  · exact (hf.2 53 (by decide)).trans (show (entryResult g E0 s).1.read (%53) = _ from rfl)
  · exact (hf.2 54 (by decide)).trans (show (entryResult g E0 s).1.read (%54) = _ from rfl)
  · exact (hf.2 55 (by decide)).trans (show (entryResult g E0 s).1.read (%55) = _ from rfl)
  · exact (hf.2 56 (by decide)).trans (show (entryResult g E0 s).1.read (%56) = _ from rfl)
  · exact (hf.2 57 (by decide)).trans (show (entryResult g E0 s).1.read (%57) = _ from rfl)
  · exact (hf.2 58 (by decide)).trans (show (entryResult g E0 s).1.read (%58) = _ from rfl)
  · exact (hf.2 59 (by decide)).trans (show (entryResult g E0 s).1.read (%59) = _ from rfl)
  · exact (hf.2 60 (by decide)).trans (show (entryResult g E0 s).1.read (%60) = _ from rfl)
  · exact (hf.2 61 (by decide)).trans (show (entryResult g E0 s).1.read (%61) = _ from rfl)
  · exact frame_slot_value g E0 _ s hf 9
  · exact frame_slot_value g E0 _ s hf 17
  · simp only [Helpers.correctionEnv,mlir_env]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate

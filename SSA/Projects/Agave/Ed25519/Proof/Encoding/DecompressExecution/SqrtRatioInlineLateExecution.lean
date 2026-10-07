import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineLateMemory

/-! The exact 470 original instructions from pc577 to the output cutpoint,
composed from checked serializer, helper-call, and root-correction segments. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate
open LeanMLIR.RIR SerialFieldMul Inline
open Reduce64.Execution (SmallRange)
open Inline956 (byte)
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
attribute [local irreducible] ToBytes.machine ToBytes.storeBytes SerialFieldMul.machine

/-- Only concrete register and memory facts are required at the cutpoint. -/
structure At577 (g : Globals) (E0 E : Env program.Γ) (s t : GlobalState)
    (a b : Pow22501.TightWords) : Prop where
  scratch : ScratchFrame s t
  frame : SerializerFrame.Frame 84 (entryResult g E0 s).1 E
  e85 : E.read (%85) = .value ((slot s 13).add 8#64)
  e87 : E.read (%87) = .value ((slot s 13).add 16#64)
  e89 : E.read (%89) = .value ((slot s 13).add 24#64)
  e91 : E.read (%91) = .value ((slot s 13).add 32#64)
  e236 : E.read (%236) = .value (byte (equalWords (wordCheck a b) a))
  e430 : E.read (%430) = .value (byte (equalWords (wordCheck a b) (negativeWord a)))
  check : readLimbs t (slot s 13) = (wordCheck a b).limbs
  candidate : readLimbs t (slot s 17) = (wordCandidate a b).limbs
  product : readLimbs t (slot s 11) = ((negativeWord a).mul sqrtM1Word).limbs

theorem registers577 (g : Globals) (E0 E : Env program.Γ) (s t : GlobalState)
    (a b : Pow22501.TightWords) (h : At577 g E0 E s t a b) :
    Inline577.Registers E (slot s 13) (slot s 11) (slot s 1) (slot s 0) := by
  have hc := constants577 g E0 E s h.frame
  exact ⟨hc,⟨frame_slot_value g E0 E s h.frame 13,h.e85,h.e87,h.e89,h.e91⟩,
    ⟨frame_slot_value g E0 E s h.frame 11,hc.c3,hc.c4,hc.c5,hc.c6⟩,
    frame_slot_value g E0 E s h.frame 1,frame_slot_value g E0 E s h.frame 0⟩

/-- Exact late execution reaches the actual output stores with the specified
word-level square root and normalized success flag, preserving caller memory. -/
theorem segment (g : Globals) (E0 E : Env program.Γ) (s t : GlobalState)
    (out : Pointer) (a b : Pow22501.TightWords) (hwf : s.WF)
    (ho : SmallRange s.mem out 48) (hg : SmallRange s.mem g.address0 40)
    (hgi : readLimbs s g.address0 = sqrtM1Word.limbs)
    (hout : E0.read (%arg0) = .value out) (h : At577 g E0 E s t a b) :
    ∃ (F : Env program.Γ) (d : ExecutionOutputData),
      Cutpoint.segment (program sqrtRatioPrimitives g) 0 577 470 E t =
        .value (F,state1047 g s t a b) ∧
      ExecutionOutputReady F (state1047 g s t a b) out d ∧
      (state1047 g s t a b).mem.readAt d.root 320 = limbBytes (wordSqrt a b).2.limbs ∧
      d.first ||| d.second = byte (wordSqrt a b).1 ∧
      ScratchFrame s (state1047 g s t a b) := by
  have hs := h.scratch
  obtain ⟨F,hfirst,hframe⟩ := Inline577.segment sqrtRatioPrimitives g E t
    (slot s 13) (slot s 11) (slot s 1) (slot s 0)
    hs.wf (hs.slots 13) (hs.slots 11) (hs.slots 1) (hs.slots 0)
    (registers577 g E0 E s t a b h)
  change Cutpoint.segment (program sqrtRatioPrimitives g) 0 577 370 E t =
    .value (F,state947 s t) at hfirst
  have hf : SerializerFrame.Frame 84 (entryResult g E0 s).1 F :=
    h.frame.trans (hframe.mono (by decide))
  have hslots (i : Fin 22) : F.read (slotRegister i) = .value (slot s i) :=
    frame_slot_value g E0 F s hf i
  have h430 : F.read (%430) = .value (byte (equalWords (wordCheck a b) (negativeWord a))) :=
    (hframe.2 430 (by decide)).trans h.e430
  have h236 : F.read (%236) = .value (byte (equalWords (wordCheck a b) a)) :=
    (hframe.2 236 (by decide)).trans h.e236
  have h52 : F.read (%52) = .value g.address0 :=
    (hf.2 52 (by decide)).trans (entry_sqrtM1 g E0 s)
  have hs947 := state947_scratch s t hs
  have hmiddle := Helpers.segment_947_956 g F (state947 s t) (slot s 1) (slot s 0)
    (slot s 9) g.address0 (slot s 17) (byte (equalWords (wordCheck a b) (negativeWord a)))
    hs947.wf (hs947.slots 1) (hs947.slots 0) (hs947.slots 9)
    (hs947.old_live hwf hg) (hs947.slots 17) (hslots 1) (hslots 0)
    (hslots 9) h52 (hslots 17) h430
  let G : Env program.Γ := Helpers.correctionEnv F
    (Helpers.comparison (state947 s t) (slot s 1) (slot s 0))
    (byte (equalWords (wordCheck a b) (negativeWord a)))
  have hcorrect : Helpers.comparison (state947 s t) (slot s 1) (slot s 0) |||
      byte (equalWords (wordCheck a b) (negativeWord a)) = correction a b := by
    rw [state947_comparison s t a b hs h.check h.product]
    unfold byte correction
    rw [Helpers.correction_byte,Bool.or_comm]
    rfl
  have hg956 : Inline956.Registers G (slot s 17) (slot s 9) (correction a b) := by
    rw [← hcorrect]
    exact registers956 g E0 F s hf _ _
  have hs956 := state956_scratch g s t hs
  have hx : readLimbs (state956 g s t) (slot s 17) = (wordCandidate a b).limbs :=
    (state956_candidate g s t).trans h.candidate
  have hy := state956_replacement g s t a b hwf hs hg hgi h.candidate
  have htail := Inline956.tail91 g G (state956 g s t) (slot s 17) (slot s 9)
    (correction a b) (wordCandidate a b).limbs (sqrtM1Word.mul (wordCandidate a b)).limbs
    hg956 hs956.wf (hs956.slots 17) (hs956.slots 9) hx hy
  have hGframe : SerializerFrame.Frame 431 E G :=
    hframe.trans ((correction_frame F _ _).mono (by decide))
  have hGout : G.read (%arg0) = .value out := by
    change G.args 0 = _
    rw [hGframe.1,h.frame.1,entry_args]
    exact hout
  have hGfirst : G.read (%430) = .value (byte (equalWords (wordCheck a b) (negativeWord a))) :=
    (hGframe.2 430 (by decide)).trans h.e430
  have hGsecond : G.read (%236) = .value (byte (equalWords (wordCheck a b) a)) :=
    (hGframe.2 236 (by decide)).trans h.e236
  have hGforty : G.read (%1) = .value 40#64 :=
    (hGframe.2 1 (by decide)).trans (constants577 g E0 E s h.frame).c1
  have hready := Inline956.output_ready G (state956 g s t) out (slot s 17) (slot s 9)
    (correction a b) (byte (equalWords (wordCheck a b) (negativeWord a)))
    (byte (equalWords (wordCheck a b) a))
    (wordCandidate a b).limbs (sqrtM1Word.mul (wordCandidate a b)).limbs
    hg956 hs956.wf (hs956.slots 17) (hs956.old_live hwf ho)
    (Or.inl (Ne.symm (slot_caller_disjoint s hwf 17 out ho)))
    hGout hGfirst hGsecond hGforty
  refine ⟨_,_,?_,hready,state1047_root g s t a b hs,Inline956.flag_sqrt a b,
    state1047_scratch g s t a b hs⟩
  rw [show 470 = 370 + 100 from rfl,segment_append]
  simp only [EffectM.bind_eq,hfirst,PoisonOr.value_bind,Nat.reduceAdd]
  rw [show 100 = 9 + 91 from rfl,segment_append]
  simp only [EffectM.bind_eq,hmiddle,PoisonOr.value_bind,Nat.reduceAdd]
  exact htail

/-- Existential-state interface for composing the checked early and late slices. -/
theorem reaches_output (g : Globals) (E0 E : Env program.Γ) (s t : GlobalState)
    (out : Pointer) (a b : Pow22501.TightWords) (hwf : s.WF)
    (ho : SmallRange s.mem out 48) (hg : SmallRange s.mem g.address0 40)
    (hgi : readLimbs s g.address0 = sqrtM1Word.limbs)
    (hout : E0.read (%arg0) = .value out) (h : At577 g E0 E s t a b) :
    ∃ (F : Env program.Γ) (z : GlobalState) (d : ExecutionOutputData),
      Cutpoint.segment (program sqrtRatioPrimitives g) 0 577 470 E t = .value (F,z) ∧
      ExecutionOutputReady F z out d ∧ z.mem.readAt d.root 320 = limbBytes (wordSqrt a b).2.limbs ∧
      d.first ||| d.second = byte (wordSqrt a b).1 ∧ ScratchFrame s z := by
  obtain ⟨F,d,hF,hr,hm,hb,hframe⟩ := segment g E0 E s t out a b hwf ho hg hgi hout h
  exact ⟨F,_,d,hF,hr,hm,hb,hframe⟩

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.InlineLate

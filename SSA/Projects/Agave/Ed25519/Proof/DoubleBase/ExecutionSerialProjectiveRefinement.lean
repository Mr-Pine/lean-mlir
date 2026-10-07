import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialReturnRefinement

/-! Readback of the real three-multiplication projective conversion and copy.
The round boundary preserves a valid projective accumulator and tight limbs. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readField readPoint readProjective)
set_option maxRecDepth 10000

def completedAsProjective (P : SerialPoint.LimbPoint) : SerialPoint.LimbPoint :=
  let Q := SerialPoint.asExtended P
  ⟨Q.X, Q.Y, Q.Z, fun _ => 0⟩

theorem projectiveState_readProjective (s : GlobalState) (out input : Pointer)
    (hout : Buffer s.mem out 120) (hinput : Buffer s.mem input 160)
    (hne : out.id ≠ input.id)
    (hP : SerialPoint.PointBounded (readPoint s input)) :
    readProjective (projectiveState s out input) out = completedAsProjective (readPoint s input) := by
  let s₁ := fieldState s out input (input.add 120)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  let s₃ := fieldState s₂ (out.add 80) (input.add 80) (input.add 120)
  have ho₁ := fieldState_buffer hout out input (input.add 120)
  have ho₂ := fieldState_buffer ho₁ (out.add 40) (input.add 40) (input.add 80)
  have hr₁ : readPoint s₁ input = readPoint s input := fieldState_readPoint_ne _ _ _ _ _ hne
  have hr₂ : readPoint s₂ input = readPoint s input :=
    (fieldState_readPoint_ne _ _ _ _ _ (by simpa only [Pointer.add_id] using hne)).trans hr₁
  have hb₁ : SerialPoint.PointBounded (readPoint s₁ input) := hr₁.symm ▸ hP
  have hb₂ : SerialPoint.PointBounded (readPoint s₂ input) := hr₂.symm ▸ hP
  have readX₁ : readField s₁ input = readField s input := congrArg PointArithmetic.Extended.X hr₁
  have readY₁ : readField s₁ (input.add 40) = readField s (input.add 40) := congrArg PointArithmetic.Extended.Y hr₁
  have readZ₁ : readField s₁ (input.add 80) = readField s (input.add 80) := congrArg PointArithmetic.Extended.Z hr₁
  have readZ₂ : readField s₂ (input.add 80) = readField s (input.add 80) := congrArg PointArithmetic.Extended.Z hr₂
  have readT₂ : readField s₂ (input.add 120) = readField s (input.add 120) := congrArg PointArithmetic.Extended.T hr₂
  have hd (a b : Fin 3) (hab : a ≠ b) :
      (Range.of (out.add (BitVec.ofNat 64 (40 * a.val))) 320).Disjoint
        (Range.of (out.add (BitVec.ofNat 64 (40 * b.val))) 320) := by
    apply SerialPoint.Execution.subranges_disjoint hout (ni := 40) (nj := 40)
      (by have := a.isLt; omega) (by have := b.isLt; omega)
    have : a.val ≠ b.val := fun h => hab (Fin.ext h)
    omega
  have h0 := hout.slice 0 40 (by decide)
  have h0₁ := ho₁.slice 0 40 (by decide)
  have h0₂ := ho₂.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at h0 h0₁ h0₂
  have hX₁ : readField s₁ out = SerialPoint.mul (readField s input) (readField s (input.add 120)) :=
    fieldState_readField_correct s out input (input.add 120) h0 hP.1 hP.2.2.2
  have hX₂ : readField s₂ out = readField s₁ out :=
    fieldState_readField_frame _ _ _ _ _ (ho₁.slice 40 40 (by decide)) h0₁
      (by simpa using hd 0 1 (by decide))
  have hX₃ : readField s₃ out = readField s₂ out :=
    fieldState_readField_frame _ _ _ _ _ (ho₂.slice 80 40 (by decide)) h0₂
      (by simpa using hd 0 2 (by decide))
  have hY₂ : readField s₂ (out.add 40) = SerialPoint.mul (readField s (input.add 40)) (readField s (input.add 80)) := by
    simpa only [readY₁, readZ₁] using fieldState_readField_correct
      s₁ (out.add 40) (input.add 40) (input.add 80)
      (ho₁.slice 40 40 (by decide)) hb₁.2.1 hb₁.2.2.1
  have hY₃ : readField s₃ (out.add 40) = readField s₂ (out.add 40) :=
    fieldState_readField_frame _ _ _ _ _ (ho₂.slice 80 40 (by decide)) (ho₂.slice 40 40 (by decide))
      (by simpa using hd 1 2 (by decide))
  have hZ₃ : readField s₃ (out.add 80) = SerialPoint.mul (readField s (input.add 80)) (readField s (input.add 120)) := by
    simpa only [readZ₂, readT₂] using fieldState_readField_correct
      s₂ (out.add 80) (input.add 80) (input.add 120)
      (ho₂.slice 80 40 (by decide)) hb₂.2.2.1 hb₂.2.2.2
  apply PointArithmetic.Extended.ext
  · exact hX₃.trans (hX₂.trans hX₁)
  · exact hY₃.trans hY₂
  · exact hZ₃
  · rfl

theorem readProjective_copy (s : GlobalState) (out input : Pointer)
    (hout : Buffer s.mem out 120) (hinput : Buffer s.mem input 120) :
    readProjective {s with mem := s.mem.storeAt out (s.mem.readAt input 960)} out =
      readProjective s input := by
  have hword (c : Fin 3) (i : Fin 5) :
      (s.mem.storeAt out (s.mem.readAt input 960)).readAt
          (out.add (BitVec.ofNat 64 (40*c.val + 8*i.val))) 64 =
        s.mem.readAt (input.add (BitVec.ofNat 64 (40*c.val + 8*i.val))) 64 := by
    have hk : 40*c.val + 8*i.val < 2^64 := by omega
    have hbits : (BitVec.ofNat 64 (40*c.val + 8*i.val)).toNat * 8 + 64 ≤ 960 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
      omega
    rw [MemoryState.readAt_storeAt_add hout.fits
      (Reduce64.Execution.SmallRange.no_wrap hout (k := 40*c.val + 8*i.val) (by omega)) hbits]
    exact (MemoryState.readAt_add_of_readAt hinput.fits
      (Reduce64.Execution.SmallRange.no_wrap hinput (k := 40*c.val + 8*i.val) (by omega)) hbits rfl).symm
  have hfield (c : Fin 3) :
      readField {s with mem := s.mem.storeAt out (s.mem.readAt input 960)}
          (out.add (BitVec.ofNat 64 (40*c.val))) =
        readField s (input.add (BitVec.ofNat 64 (40*c.val))) := by
    funext i
    simp only [readField, SerialFieldMul.unsigned, SerialFieldMul.readLimbs,
      Pointer.add_add, ← BitVec.ofNat_add, hword]
  apply PointArithmetic.Extended.ext
  · simpa [readProjective] using hfield 0
  · simpa [readProjective] using hfield 1
  · simpa [readProjective] using hfield 2
  · rfl

theorem projectiveRoundState_readProjective (s : GlobalState)
    (temporary completed projective : Pointer)
    (ht : Buffer s.mem temporary 120) (hc : Buffer s.mem completed 160)
    (hp : Buffer s.mem projective 120) (hne : temporary.id ≠ completed.id)
    (hP : SerialPoint.PointBounded (readPoint s completed)) :
    readProjective (projectiveRoundState s temporary completed projective) projective =
      completedAsProjective (readPoint s completed) := by
  unfold projectiveRoundState
  rw [readProjective_copy _ projective temporary (projectiveState_buffer hp _ _)
    (projectiveState_buffer ht _ _)]
  exact projectiveState_readProjective s temporary completed ht hc hne hP

theorem projectiveRoundState_buffer (h : Buffer s.mem q bytes)
    (temporary completed projective : Pointer) :
    Buffer (projectiveRoundState s temporary completed projective).mem q bytes :=
  (projectiveState_buffer h temporary completed).storeAt _ _

theorem projectiveRoundState_wf (s : GlobalState) (temporary completed projective : Pointer)
    (hwf : s.WF) : (projectiveRoundState s temporary completed projective).WF :=
  (projectiveState_wf s temporary completed hwf).storeAt

theorem completedAsProjective_tight (P : SerialPoint.LimbPoint)
    (h : SerialPoint.PointBounded P) : SerialPoint.PointTight (completedAsProjective P) :=
  ⟨(SerialPoint.asExtended_tight P h).1, (SerialPoint.asExtended_tight P h).2.1,
    (SerialPoint.asExtended_tight P h).2.2.1, by intro i; change 0 < 2^52; decide⟩

theorem completedAsProjective_represents (P : SerialPoint.LimbPoint) (V : GroupPoint)
    (h : Tables.Represents (SerialPoint.pointValue (SerialPoint.asExtended P)) V) :
    ProjectiveRepresents (completedAsProjective P) V :=
  ⟨_, h, rfl, rfl, rfl⟩

/-- The actual round-end block passes a tight, valid accumulator to either
another ladder iteration or the verified result block. -/
theorem serial_projective_run_represents (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (E : ⟪serialKernel.Γ⟫) (temporary completed projective : Pointer)
    (i : Fin 256) (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 120) (hc : Buffer s.mem completed 160)
    (hp : Buffer s.mem projective 120) (hpt : projective.id ≠ temporary.id)
    (htc : temporary.id ≠ completed.id)
    (hP : SerialPoint.PointBounded (readPoint s completed)) (V : GroupPoint)
    (hrep : Tables.Represents (SerialPoint.pointValue
      (SerialPoint.asExtended (readPoint s completed))) V) :
    (serialKernel p g).runFrom (projectiveInput E temporary completed projective i) 28 s =
      (serialKernel p g).runFrom (projectiveResult E temporary completed projective i)
        (if i.val = 0 then 34 else 35) (projectiveRoundState s temporary completed projective) ∧
    (projectiveRoundState s temporary completed projective).WF ∧
    SerialPoint.PointTight (readProjective (projectiveRoundState s temporary completed projective) projective) ∧
    ProjectiveRepresents (readProjective (projectiveRoundState s temporary completed projective) projective) V := by
  refine ⟨serial_projective_run p g hfield E temporary completed projective i s hwf ht hc hp hpt,
    projectiveRoundState_wf s temporary completed projective hwf, ?_, ?_⟩
  · rw [projectiveRoundState_readProjective s temporary completed projective ht hc hp htc hP]
    exact completedAsProjective_tight _ hP
  · rw [projectiveRoundState_readProjective s temporary completed projective ht hc hp htc hP]
    exact completedAsProjective_represents _ V hrep

end Agave.Ed25519.DoubleBase.RIR

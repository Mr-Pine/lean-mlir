import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialConversionRefinement
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialReturn

/-! Write frames for the actual serial conversion and return stores. These
compose at the byte-range boundary and retain every caller allocation. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (WritesOnly readField readPoint readProjective)

theorem writesOnly_trans {p : Pointer} (h₁ : WritesOnly p bytes s₀ s₁)
    (h₂ : WritesOnly p bytes s₁ s₂) : WritesOnly p bytes s₀ s₂ := by
  refine ⟨h₂.wellFormed, h₁.allocationMonotone.trans h₂.allocationMonotone, ?_, ?_⟩
  · intro id
    exact (h₂.allocationShape id).trans (h₁.allocationShape id)
  · intro q bits hd
    exact (h₂.readFrame q bits hd).trans (h₁.readFrame q bits hd)

theorem range_disjoint_subrange {p : Pointer} (h : Buffer m p bytes)
    (hd : (Range.of q bits).Disjoint (Range.of p (8 * bytes)))
    (hk : k + count ≤ bytes) :
    (Range.of q bits).Disjoint
      (Range.of (p.add (BitVec.ofNat 64 k)) (8 * count)) := by
  have hoff := Pointer.offsetInBits_add (Reduce64.Execution.SmallRange.no_wrap h (k := k) (by omega))
  have hk64 : k < 2^64 := by have := Reduce64.Execution.SmallRange.offset_lt h; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at hoff
  simp only [Range.Disjoint, Range.of, Pointer.add_id, hoff] at hd ⊢
  rcases hd with hne | hbefore | hafter
  · exact Or.inl hne
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem writesOnly_widen {p : Pointer} (h : WritesOnly (p.add (BitVec.ofNat 64 k)) count s t)
    (hp : Buffer s.mem p bytes) (hk : k + count ≤ bytes) :
    WritesOnly p bytes s t := by
  refine ⟨h.wellFormed, h.allocationMonotone, h.allocationShape, ?_⟩
  intro q bits hd
  exact h.readFrame q bits (range_disjoint_subrange hp hd hk)

theorem fieldState_writesOnly (s : GlobalState) (out a b : Pointer)
    (hwf : s.WF) (hout : Buffer s.mem out 40) :
    WritesOnly out 40 s (fieldState s out a b) := by
  refine ⟨fieldState_wf _ _ _ _ hwf, le_refl _, ?_, ?_⟩
  · intro id
    exact SerialPoint.Execution.storeLimbs_allocationShape s.mem out _ id
  · intro q bits hd
    exact SerialPoint.Execution.readAt_storeLimbs_frame s.mem out q _ bits hout hd

theorem squareState_writesOnly (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : Buffer s.mem out 40) :
    WritesOnly out 40 s (squareState s out input) := by
  refine ⟨squareState_wf _ _ _ hwf, le_refl _, ?_, ?_⟩
  · intro id
    exact SerialPoint.Execution.storeLimbs_allocationShape s.mem out _ id
  · intro q bits hd
    exact SerialPoint.Execution.readAt_storeLimbs_frame s.mem out q _ bits hout hd

theorem squareState_readField_ne (s : GlobalState) (out input q : Pointer)
    (hne : out.id ≠ q.id) :
    readField (squareState s out input) q = readField s q := by
  unfold readField
  rw [show SerialFieldMul.readLimbs (squareState s out input) q = SerialFieldMul.readLimbs s q from
    SerialPoint.Execution.readLimbs_storeLimbs_ne s out q _ hne]

theorem squareState_readField_frame (s : GlobalState) (out input q : Pointer)
    (ho : Buffer s.mem out 40) (hq : Buffer s.mem q 40)
    (hd : (Range.of q 320).Disjoint (Range.of out 320)) :
    readField (squareState s out input) q = readField s q := by
  unfold readField
  rw [show SerialFieldMul.readLimbs (squareState s out input) q = SerialFieldMul.readLimbs s q from
    SerialPoint.Execution.readLimbs_storeLimbs_frame s out q _ ho hq hd]

theorem squareState_readField_correct (s : GlobalState) (out input : Pointer)
    (ho : Buffer s.mem out 40) (ha : SerialFieldMul.Bounded (readField s input)) :
    readField (squareState s out input) out = SerialPoint.sq (readField s input) := by
  unfold readField
  rw [show SerialFieldMul.readLimbs (squareState s out input) out =
      SerialPoint.squareMachine (SerialFieldMul.readLimbs s input) from
    SerialPoint.Execution.readLimbs_storeLimbs s out _ ho]
  exact SerialPoint.squareMachine_unsigned _ ha

theorem fieldState_readProjective_ne (s : GlobalState) (out a b q : Pointer)
    (hne : out.id ≠ q.id) :
    readProjective (fieldState s out a b) q = readProjective s q := by
  apply PointArithmetic.Extended.ext
  all_goals first | rfl |
    (apply fieldState_readField_ne; simpa only [Pointer.add_id] using hne)

theorem squareState_readProjective_ne (s : GlobalState) (out input q : Pointer)
    (hne : out.id ≠ q.id) :
    readProjective (squareState s out input) q = readProjective s q := by
  apply PointArithmetic.Extended.ext
  all_goals first | rfl |
    (apply squareState_readField_ne; simpa only [Pointer.add_id] using hne)

theorem completedState_writesOnly (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : Buffer s.mem out 160) :
    WritesOnly out 160 s (completedState s out input) := by
  let s₁ := fieldState s out input (input.add 120)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  let s₃ := fieldState s₂ (out.add 80) (input.add 80) (input.add 120)
  have h₁ : WritesOnly out 160 s s₁ := by
    apply writesOnly_widen (p := out) (k := 0) (count := 40) (hp := hout) (hk := by decide)
    simpa only [s₁, BitVec.ofNat_eq_ofNat, Pointer.add_zero] using
      fieldState_writesOnly s out input (input.add 120) hwf
        (by simpa using hout.slice 0 40 (by decide))
  have ho₁ : Buffer s₁.mem out 160 := h₁.smallRange hout
  have h₂ : WritesOnly out 160 s₁ s₂ :=
    writesOnly_widen (fieldState_writesOnly s₁ _ _ _ h₁.wellFormed
      (ho₁.slice 40 40 (by decide))) ho₁ (by decide)
  have ho₂ : Buffer s₂.mem out 160 := h₂.smallRange ho₁
  have h₃ : WritesOnly out 160 s₂ s₃ :=
    writesOnly_widen (fieldState_writesOnly s₂ _ _ _ h₂.wellFormed
      (ho₂.slice 80 40 (by decide)))
      ho₂ (by decide)
  have ho₃ : Buffer s₃.mem out 160 := h₃.smallRange ho₂
  have h₄ : WritesOnly out 160 s₃ (completedState s out input) :=
    writesOnly_widen (fieldState_writesOnly s₃ _ _ _ h₃.wellFormed
      (ho₃.slice 120 40 (by decide)))
      ho₃ (by decide)
  exact writesOnly_trans (writesOnly_trans (writesOnly_trans h₁ h₂) h₃) h₄

theorem serialReturnState_writesOnly (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : Buffer s.mem out 160) :
    WritesOnly out 160 s (serialReturnState s out input) := by
  let s₁ := fieldState s out input (input.add 80)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  let s₃ := squareState s₂ (out.add 80) (input.add 80)
  have h₁ : WritesOnly out 160 s s₁ := by
    apply writesOnly_widen (p := out) (k := 0) (count := 40) (hp := hout) (hk := by decide)
    simpa only [s₁, BitVec.ofNat_eq_ofNat, Pointer.add_zero] using
      fieldState_writesOnly s out input (input.add 80) hwf
        (by simpa using hout.slice 0 40 (by decide))
  have ho₁ : Buffer s₁.mem out 160 := h₁.smallRange hout
  have h₂ : WritesOnly out 160 s₁ s₂ :=
    writesOnly_widen (fieldState_writesOnly s₁ _ _ _ h₁.wellFormed
      (ho₁.slice 40 40 (by decide))) ho₁ (by decide)
  have ho₂ : Buffer s₂.mem out 160 := h₂.smallRange ho₁
  have h₃ : WritesOnly out 160 s₂ s₃ :=
    writesOnly_widen (squareState_writesOnly s₂ _ _ h₂.wellFormed
      (ho₂.slice 80 40 (by decide)))
      ho₂ (by decide)
  have ho₃ : Buffer s₃.mem out 160 := h₃.smallRange ho₂
  have h₄ : WritesOnly out 160 s₃ (serialReturnState s out input) :=
    writesOnly_widen (fieldState_writesOnly s₃ _ _ _ h₃.wellFormed
      (ho₃.slice 120 40 (by decide)))
      ho₃ (by decide)
  exact writesOnly_trans (writesOnly_trans (writesOnly_trans h₁ h₂) h₃) h₄

end Agave.Ed25519.DoubleBase.RIR

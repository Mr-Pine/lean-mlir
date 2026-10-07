import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlinePrefixMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! Actual first two arithmetic calls of sqrt_ratio_i, reached from the proved
entry. No call-result or intermediate readiness hypothesis is supplied by the
caller: the scratch objects and old input reads come from entry allocation. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul
open SerialPoint.Execution

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

attribute [local irreducible] Pow2k.iterateSquare machine

theorem segment_append (f : Func) (block : Fin f.n) (first n m : Nat)
    (E : ⟪f.Γ⟫) :
    Cutpoint.segment f block first (n + m) E = (do
      let F ← Cutpoint.segment f block first n E
      Cutpoint.segment f block (first + n) m F) := by
  unfold Cutpoint.segment
  rw [List.take_add, List.foldlM_append]
  simp only [List.drop_drop]

noncomputable def afterSquare (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (v : Pointer) : GlobalState :=
  let t := (entryResult g E s).2
  { alloc := t.alloc,
    mem := storeLimbs t.mem (slot s 20) (Pow2k.iterateSquare 1 (readLimbs s v)) }

theorem first_square_segment (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (v : Pointer) (hwf : s.WF) (hv : SmallRange s.mem v 40)
    (hvreg : E.read (%arg2) = .value v) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 86 1
      (entryResult g E s).1 (entryResult g E s).2 =
      .value ((entryResult g E s).1, afterSquare g E s v) := by
  have hw : (entryResult g E s).2.WF := by
    rw [entry_state]
    exact allocate_wf s hwf _
  have hr : SmallRange (entryResult g E s).2.mem (slot s 20) 40 := by
    rw [entry_state]
    exact slot_live s hwf 20
  have hinput := entry_live g E s hwf v hv
  have hroot : (entryResult g E s).1.read (%82) = .value (slot s 20) :=
    entry_slot g E s 20
  have harg : (entryResult g E s).1.read (%arg2) = .value v := by
    change (entryResult g E s).1.args 2 = .value v
    rw [entry_args]
    exact hvreg
  have hc := Pow2k.program_call 1 (by decide) (by decide)
    (slot s 20) v (entryResult g E s).2 hw hr hinput
  rw [entry_readLimbs g E s hwf v hv] at hc
  simp only [Pow2k.program.args] at hc
  change ((do
      let returnedValues ← sqrtRatioPrimitives.pow2k
        (.cons ((entryResult g E s).1.read (%82))
          (.cons ((entryResult g E s).1.read (%arg2))
            (.cons ((entryResult g E s).1.read (%0)) .nil)))
      pure ((entryResult g E s).1.writeMany .nil returnedValues)) >>= pure)
      (entryResult g E s).2 = _
  simp only [hroot, harg, entry_first_count, sqrtRatioPrimitives,
    EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

noncomputable def afterV3 (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (v : Pointer) : GlobalState :=
  let t := afterSquare g E s v
  { alloc := t.alloc,
    mem := storeLimbs t.mem (slot s 21)
      (machine (Pow2k.iterateSquare 1 (readLimbs s v)) (readLimbs s v)) }

theorem first_mul_segment (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (v : Pointer) (hwf : s.WF) (hv : SmallRange s.mem v 40)
    (hvreg : E.read (%arg2) = .value v) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 87 1
      (entryResult g E s).1 (afterSquare g E s v) =
      .value ((entryResult g E s).1, afterV3 g E s v) := by
  have hw : (entryResult g E s).2.WF := by
    rw [entry_state]
    exact allocate_wf s hwf _
  have hlive (i : Fin 22) :
      SmallRange (entryResult g E s).2.mem (slot s i)
        (allocationSizes[i.val]'(by exact i.isLt)) := by
    rw [entry_state]
    exact slot_live s hwf i
  have hx : readLimbs (afterSquare g E s v) (slot s 20) =
      Pow2k.iterateSquare 1 (readLimbs s v) :=
    readLimbs_storeLimbs (entryResult g E s).2 (slot s 20) _ (hlive 20)
  have hy : readLimbs (afterSquare g E s v) v = readLimbs s v := by
    exact (readLimbs_storeLimbs_ne (entryResult g E s).2 (slot s 20) v
      (Pow2k.iterateSquare 1 (readLimbs s v)) (slot_caller_disjoint s hwf 20 v hv)).trans
        (entry_readLimbs g E s hwf v hv)
  have hc := kernel_call (slot s 21) (slot s 20) v (afterSquare g E s v)
    (wf_storeLimbs hw _ _) (smallRange_storeLimbs (hlive 21) _ _)
    (smallRange_storeLimbs (hlive 20) _ _) (smallRange_storeLimbs (entry_live g E s hwf v hv) _ _)
  rw [hx, hy] at hc
  simp only [SerialFieldMul.kernel.args] at hc
  have hr : (entryResult g E s).1.read (%83) = .value (slot s 21) := entry_slot g E s 21
  have ha : (entryResult g E s).1.read (%82) = .value (slot s 20) := entry_slot g E s 20
  have hb : (entryResult g E s).1.read (%arg2) = .value v := by
    change (entryResult g E s).1.args 2 = .value v
    rw [entry_args]
    exact hvreg
  change ((do
      let returnedValues ← sqrtRatioPrimitives.mul
        (.cons ((entryResult g E s).1.read (%83))
          (.cons ((entryResult g E s).1.read (%82))
            (.cons ((entryResult g E s).1.read (%arg2)) .nil)))
      pure ((entryResult g E s).1.writeMany .nil returnedValues)) >>= pure)
      (afterSquare g E s v) = _
  simp only [hr, ha, hb, sqrtRatioPrimitives, EffectM.bind_eq, EffectM.pure_eq]
  rw [hc]
  rfl

/-- All first 88 instructions execute: constants, scratch allocations, one
checked square and one checked multiplication. The result is exact v cubed. -/
theorem v3_prefix (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (v : Pointer) (hwf : s.WF) (hv : SmallRange s.mem v 40)
    (hvreg : E.read (%arg2) = .value v) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 88 E s =
      .value ((entryResult g E s).1, afterV3 g E s v) := by
  rw [show 88 = 86 + (1 + 1) from rfl, segment_append]
  simp only [EffectM.bind_eq, entry_segment, LeanMLIR.RIR.PoisonOr.value_bind]
  rw [segment_append]
  simp only [EffectM.bind_eq, first_square_segment g E s v hwf hv hvreg,
    LeanMLIR.RIR.PoisonOr.value_bind]
  exact first_mul_segment g E s v hwf hv hvreg

theorem private_store_erase (m : MemoryState) (p : Pointer) (words : Words)
    (mark : Nat) (hprivate : mark ≤ p.id.id) :
    (storeLimbs m p words).eraseFrom mark = m.eraseFrom mark := by
  simp only [storeLimbs, MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (p := p) hprivate,
    MemoryState.storeAt_eraseFrom_of_le (p := p.add _) hprivate]

/-- The two arithmetic calls only modify the proved private scratch fields. -/
theorem v3_public (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState)
    (v : Pointer) (hwf : s.WF) :
    (afterV3 g E s v).mem.eraseFrom s.alloc.nextFreeBlock = s.mem ∧
      (afterV3 g E s v).alloc.nextFreeBlock = s.alloc.nextFreeBlock + 22 := by
  constructor
  · simp only [afterV3, afterSquare]
    rw [private_store_erase _ (slot s 21) _ _ (slot_private s 21),
      private_store_erase _ (slot s 20) _ _ (slot_private s 20)]
    exact entry_public g E s hwf
  · change (entryResult g E s).2.alloc.nextFreeBlock = _
    rw [entry_state]
    exact allocate_counter s allocationSizes

/-- Field semantics is derived from the actually executed words, with the
ordinary tight-limb precondition of the field kernels. -/
theorem v3_field (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState)
    (v : Pointer) (hwf : s.WF)
    (htight : SerialPoint.Tight (unsigned (readLimbs s v))) :
    wordValue (readLimbs (afterV3 g E s v) (slot s 21)) =
      wordValue (readLimbs s v) ^ 3 := by
  have hlive : SmallRange (entryResult g E s).2.mem (slot s 21) 40 := by
    rw [entry_state]
    exact slot_live s hwf 21
  have hread : readLimbs (afterV3 g E s v) (slot s 21) =
      machine (Pow2k.iterateSquare 1 (readLimbs s v)) (readLimbs s v) :=
    readLimbs_storeLimbs (afterSquare g E s v) (slot s 21) _
      (smallRange_storeLimbs hlive _ _)
  rw [hread, machine_value _ _
    (SerialPoint.tight_bounded _ (Pow2k.iterateSquare_tight 1 _ htight))
    (SerialPoint.tight_bounded _ htight), Pow2k.iterateSquare_value 1 _ htight]
  ring

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline

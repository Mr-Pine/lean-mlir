import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeader
import SSA.Projects.SLLVM.Dialect.Semantics.ArithSemantics
set_option maxHeartbeats 400000
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Both no-wrap truncation flags emitted for the block length are valid. -/
theorem truncate_block_size (size : Nat) (hsize : size ≤ 64) :
    LLVM.trunc 32 (.value (BitVec.ofNat 64 size)) {nsw := true, nuw := true} =
      .value (BitVec.ofNat 32 size) := by
  interval_cases size <;> rfl

/-- The disjoint-or flag is justified: CHUNK_START occupies bit zero, while
ROOT|CHUNK_END occupies bits one and three. -/
theorem header_flags (active first : Bool) :
    LLVM.or
      (LLVM.select (.value (BitVec.ofBool active)) (.value 0#32) (.value 10#32))
      (LLVM.zext 32 (.value (BitVec.ofBool first))) {«disjoint» := true} =
      .value (BitVec.ofNat 32 ((if active then 0 else 10) + (if first then 1 else 0))) := by
  cases active <;> cases first <;> rfl

/-- Unsigned subtraction/minimum in the header computes the model's block
length. The offset premise rules out wraparound before the minimum. -/
theorem header_size (len off : Nat) (hlen : len ≤ 1024) (hoff : off ≤ len) :
    umin (LLVM.sub (.value (BitVec.ofNat 64 len)) (.value (BitVec.ofNat 64 off)))
      (.value 64#64) = .value (BitVec.ofNat 64 (AgaveBatchControl.blockSize len off)) := by
  have ho : off < 2^64 := by omega
  have hs : (len-off) % 18446744073709551616 = len-off := Nat.mod_eq_of_lt (by omega)
  simp only [LLVM.sub, LLVM.sub?, PoisonOr.value_bind]
  rw [BitVec.ofNat_sub_ofNat_of_le len off ho hoff]
  simp only [umin, BitVec.ult]
  unfold AgaveBatchControl.blockSize
  by_cases h : len-off < 64
  · simp [hs, h, Nat.min_eq_left (by omega : len-off ≤ 64)]
  · simp [hs, h, Nat.min_eq_right (by omega : 64 ≤ len-off)]
namespace BatchHeader

variable (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 8 → AgaveConcrete.Message) (iteration : Nat) (lane : Fin 8)

noncomputable abbrev represented := headerAt8Val (BatchEntry.entryVal8 s src len out sched panic
    (Vector.ofFn fun i => BitVec.ofNat 64 (ms i).length)) ms iteration

theorem advanced_lane :
    (show Vector (LLVM.IntW 64) 8 from values8
      (represented s src len out sched panic ms iteration) ⟨26, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨0, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms i).length iteration)).map PoisonOr.value := by rfl
  have h72 : W ⟨72, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  change (Vector.ofFn fun i : Fin 8 => LLVM.add
    ((show Vector (LLVM.IntW 64) 8 from W ⟨0, rfl⟩)[i])
    ((show Vector (LLVM.IntW 64) 8 from W ⟨72, rfl⟩)[i]))[lane.val] = _
  simp only [h0, h72, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn,
    LLVM.Ty.dense]
  simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]

theorem size_lane (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 32) 8 from values8
      (represented s src len out sched panic ms iteration) ⟨17, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 32 (AgaveBatchControl.blockSize (ms lane).length
      (batchOffset (ms lane).length iteration))) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨0, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms i).length iteration)).map PoisonOr.value := by rfl
  have h24 : W ⟨24, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (ms i).length).map PoisonOr.value := by rfl
  have h72 : W ⟨72, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  change (vtrunc 32 (vumin (Vector.ofFn fun i : Fin 8 => LLVM.sub
    ((show Vector (LLVM.IntW 64) 8 from W ⟨24, rfl⟩)[i])
    ((show Vector (LLVM.IntW 64) 8 from W ⟨0, rfl⟩)[i]))
    (W ⟨72, rfl⟩)) {nsw := true, nuw := true})[lane.val] = _
  simp only [h0, h24, h72, vtrunc, vumin, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_ofFn, LLVM.Ty.dense]
  change LLVM.trunc 32 (umin
    (LLVM.sub (.value (BitVec.ofNat 64 (ms lane).length))
      (.value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration)))) (.value 64#64))
    {nsw := true, nuw := true} = _
  have hoff : batchOffset (ms lane).length iteration ≤ (ms lane).length := by
    have := AgaveBatchControl.rootIndex_bounds (ms lane).length
    have := Nat.min_le_right iteration (AgaveBatchControl.rootIndex (ms lane).length)
    unfold batchOffset
    omega
  rw [header_size _ _ (hms lane) hoff]
  exact truncate_block_size _ (Nat.min_le_right ..)

theorem flags_lane (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 32) 8 from values8
      (represented s src len out sched panic ms iteration) ⟨20, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 32 (AgaveBatchControl.blockFlags (ms lane).length
      (batchOffset (ms lane).length iteration))) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨0, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms i).length iteration)).map PoisonOr.value := by rfl
  have h24 : W ⟨24, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (ms i).length).map PoisonOr.value := by rfl
  have h72 : W ⟨72, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  have h73 : W ⟨73, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0] := by rfl
  have h70 : W ⟨70, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 32)) [0] := by rfl
  have h69 : W ⟨69, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 32)) [10] := by rfl
  change (Vector.ofFn fun i : Fin 8 => LLVM.or
    ((vselect (vfreeze (vicmp .ugt (W ⟨24, rfl⟩)
      (Vector.ofFn fun j : Fin 8 => LLVM.add
        ((show Vector (LLVM.IntW 64) 8 from W ⟨0, rfl⟩)[j])
        ((show Vector (LLVM.IntW 64) 8 from W ⟨72, rfl⟩)[j]))))
      (W ⟨70, rfl⟩) (W ⟨69, rfl⟩))[i])
    ((vzext 32 (vicmp .eq (W ⟨0, rfl⟩) (W ⟨73, rfl⟩)))[i])
    {«disjoint» := true})[lane.val] = _
  simp only [h0, h24, h72, h73, h70, h69, vfreeze, vicmp, vselect, vzext,
    Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, LLVM.Ty.dense]
  change LLVM.or (LLVM.select (LLVM.freeze (LLVM.icmp .ugt
    (.value (BitVec.ofNat 64 (ms lane).length))
    (LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration))) (.value 64#64))))
    (.value 0#32) (.value 10#32))
    (LLVM.zext 32 (LLVM.icmp .eq (.value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration)))
      (.value 0#64))) {«disjoint» := true} = _
  have hadd : LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration)))
      (.value 64#64) = .value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration + 64)) := by
    simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]
  rw [hadd, batchOffset_llvm_active _ _ (hms lane)]
  have hoff := batchOffset_le_960 (ms lane).length iteration (hms lane)
  have heq : LLVM.icmp .eq (.value (BitVec.ofNat 64 (batchOffset (ms lane).length iteration)))
      (.value 0#64) = .value (BitVec.ofBool (decide (batchOffset (ms lane).length iteration = 0))) := by
    have hm : batchOffset (ms lane).length iteration % 18446744073709551616 =
      batchOffset (ms lane).length iteration := Nat.mod_eq_of_lt (by omega)
    simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind]
    by_cases hz : batchOffset (ms lane).length iteration = 0
    · simp [hz]
    · have hb : BitVec.ofNat 64 (batchOffset (ms lane).length iteration) ≠ 0#64 := by
        intro hb
        have ht := congrArg BitVec.toNat hb
        simp only [BitVec.toNat_ofNat] at ht
        omega
      have hbeq : (BitVec.ofNat 64 (batchOffset (ms lane).length iteration) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hb
      simp [hz, hbeq]
  rw [heq]
  change LLVM.or (LLVM.select (.value (BitVec.ofBool (decide (iteration < AgaveBatchControl.rootIndex (ms lane).length))))
    (.value 0#32) (.value 10#32))
    (LLVM.zext 32 (.value (BitVec.ofBool (decide (batchOffset (ms lane).length iteration = 0)))))
    {«disjoint» := true} = _
  rw [header_flags]
  have ha := AgaveBatchControl.active_iff_before_root (ms lane).length iteration
  change (¬(ms lane).length ≤ batchOffset (ms lane).length iteration + 64 ↔
    iteration < AgaveBatchControl.rootIndex (ms lane).length) at ha
  congr 2
  unfold AgaveBatchControl.blockFlags
  by_cases ha' : iteration < AgaveBatchControl.rootIndex (ms lane).length
  · have hn : ¬ (ms lane).length ≤ batchOffset (ms lane).length iteration + 64 := ha.mpr ha'
    simp [ha', hn]
  · have hn : (ms lane).length ≤ batchOffset (ms lane).length iteration + 64 := by omega
    simp [ha', hn]

end BatchHeader
end AgaveLatticeHash.MLIR

#print axioms AgaveLatticeHash.MLIR.BatchHeader.advanced_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader.size_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader.flags_lane

/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeaderSemantics
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchPaths16
import SSA.Projects.Agave.LatticeHash.MLIR.ByteSelect
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
namespace AgaveLatticeHash.MLIR.BatchHeader16
open LeanMLIR SLLVM
open InstCombine (LLVM)

variable (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) (lane : Fin 8)

/-- Exact sixteen-lane header valuation at the scalar-prefix invariant. -/
noncomputable abbrev represented := headerAt16Val (BatchEntry16.entryVal16 s src len out sched panic
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length)
    (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length)) ms iteration

theorem advanced_lo_lane :
    (show Vector (LLVM.IntW 64) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨66, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration + 64)) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨24, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms ⟨i.val, by omega⟩).length iteration)).map PoisonOr.value := by
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val])) = _
    simp only [Vector.map_ofFn, Vector.getElem_ofFn, Function.comp_def]
  have h72 : W ⟨119, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  change (Vector.ofFn fun i : Fin 8 => LLVM.add
    ((show Vector (LLVM.IntW 64) 8 from W ⟨24, rfl⟩)[i])
    ((show Vector (LLVM.IntW 64) 8 from W ⟨119, rfl⟩)[i]))[lane.val] = _
  simp only [h0, h72, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn,
    LLVM.Ty.dense]
  simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]

theorem size_lo_lane (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨56, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 32 (AgaveBatchControl.blockSize (ms ⟨lane.val, by omega⟩).length
      (batchOffset (ms ⟨lane.val, by omega⟩).length iteration))) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨24, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms ⟨i.val, by omega⟩).length iteration)).map PoisonOr.value := by
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val])) = _
    simp only [Vector.map_ofFn, Vector.getElem_ofFn, Function.comp_def]
  have h24 : W ⟨28, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length).map PoisonOr.value := by rfl
  have h72 : W ⟨119, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  change (vtrunc 32 (vumin (Vector.ofFn fun i : Fin 8 => LLVM.sub
    ((show Vector (LLVM.IntW 64) 8 from W ⟨28, rfl⟩)[i])
    ((show Vector (LLVM.IntW 64) 8 from W ⟨24, rfl⟩)[i]))
    (W ⟨119, rfl⟩)) {nsw := true, nuw := true})[lane.val] = _
  simp only [h0, h24, h72, vtrunc, vumin, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_ofFn, LLVM.Ty.dense]
  change LLVM.trunc 32 (umin
    (LLVM.sub (.value (BitVec.ofNat 64 (ms ⟨lane.val, by omega⟩).length))
      (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration)))) (.value 64#64))
    {nsw := true, nuw := true} = _
  have hoff : batchOffset (ms ⟨lane.val, by omega⟩).length iteration ≤ (ms ⟨lane.val, by omega⟩).length := by
    have := AgaveBatchControl.rootIndex_bounds (ms ⟨lane.val, by omega⟩).length
    have := Nat.min_le_right iteration (AgaveBatchControl.rootIndex (ms ⟨lane.val, by omega⟩).length)
    unfold batchOffset
    omega
  rw [header_size _ _ (hms _) hoff]
  exact truncate_block_size _ (Nat.min_le_right ..)

theorem flags_lo_lane (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨61, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 32 (AgaveBatchControl.blockFlags (ms ⟨lane.val, by omega⟩).length
      (batchOffset (ms ⟨lane.val, by omega⟩).length iteration))) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨24, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms ⟨i.val, by omega⟩).length iteration)).map PoisonOr.value := by
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val])) = _
    simp only [Vector.map_ofFn, Vector.getElem_ofFn, Function.comp_def]
  have h24 : W ⟨28, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length).map PoisonOr.value := by rfl
  have h72 : W ⟨119, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  have h73 : W ⟨128, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0] := by rfl
  have h70 : W ⟨117, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 32)) [0] := by rfl
  have h69 : W ⟨116, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 32)) [10] := by rfl
  change (Vector.ofFn fun i : Fin 8 => LLVM.or
    ((vselect ((vicmp .ugt (W ⟨28, rfl⟩)
      (Vector.ofFn fun j : Fin 8 => LLVM.add
        ((show Vector (LLVM.IntW 64) 8 from W ⟨24, rfl⟩)[j])
        ((show Vector (LLVM.IntW 64) 8 from W ⟨119, rfl⟩)[j]))))
      (W ⟨117, rfl⟩) (W ⟨116, rfl⟩))[i])
    ((vzext 32 (vicmp .eq (W ⟨24, rfl⟩) (W ⟨128, rfl⟩)))[i])
    {«disjoint» := true})[lane.val] = _
  simp only [h0, h24, h72, h73, h70, h69, vicmp, vselect, vzext,
    Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, LLVM.Ty.dense]
  change LLVM.or (LLVM.select ((LLVM.icmp .ugt
    (.value (BitVec.ofNat 64 (ms ⟨lane.val, by omega⟩).length))
    (LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration))) (.value 64#64))))
    (.value 0#32) (.value 10#32))
    (LLVM.zext 32 (LLVM.icmp .eq (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration)))
      (.value 0#64))) {«disjoint» := true} = _
  have hadd : LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration)))
      (.value 64#64) = .value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration + 64)) := by
    simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]
  rw [hadd, batchOffset_llvm_active _ _ (hms _)]
  have hoff := batchOffset_le_960 (ms ⟨lane.val, by omega⟩).length iteration (hms _)
  have heq : LLVM.icmp .eq (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration)))
      (.value 0#64) = .value (BitVec.ofBool (decide (batchOffset (ms ⟨lane.val, by omega⟩).length iteration = 0))) := by
    have hm : batchOffset (ms ⟨lane.val, by omega⟩).length iteration % 18446744073709551616 =
      batchOffset (ms ⟨lane.val, by omega⟩).length iteration := Nat.mod_eq_of_lt (by omega)
    simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind]
    by_cases hz : batchOffset (ms ⟨lane.val, by omega⟩).length iteration = 0
    · simp [hz]
    · have hb : BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration) ≠ 0#64 := by
        intro hb
        have ht := congrArg BitVec.toNat hb
        simp only [BitVec.toNat_ofNat] at ht
        omega
      have hbeq : (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val, by omega⟩).length iteration) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hb
      simp [hz, hbeq]
  rw [heq]
  change LLVM.or (LLVM.select (.value (BitVec.ofBool (decide (iteration < AgaveBatchControl.rootIndex (ms ⟨lane.val, by omega⟩).length))))
    (.value 0#32) (.value 10#32))
    (LLVM.zext 32 (.value (BitVec.ofBool (decide (batchOffset (ms ⟨lane.val, by omega⟩).length iteration = 0)))))
    {«disjoint» := true} = _
  rw [header_flags]
  have ha := AgaveBatchControl.active_iff_before_root (ms ⟨lane.val, by omega⟩).length iteration
  change (¬(ms ⟨lane.val, by omega⟩).length ≤ batchOffset (ms ⟨lane.val, by omega⟩).length iteration + 64 ↔
    iteration < AgaveBatchControl.rootIndex (ms ⟨lane.val, by omega⟩).length) at ha
  congr 2
  unfold AgaveBatchControl.blockFlags
  by_cases ha' : iteration < AgaveBatchControl.rootIndex (ms ⟨lane.val, by omega⟩).length
  · have hn : ¬ (ms ⟨lane.val, by omega⟩).length ≤ batchOffset (ms ⟨lane.val, by omega⟩).length iteration + 64 := ha.mpr ha'
    simp [ha', hn]
  · have hn : (ms ⟨lane.val, by omega⟩).length ≤ batchOffset (ms ⟨lane.val, by omega⟩).length iteration + 64 := by omega
    simp [ha', hn]


theorem advanced_hi_lane :
    (show Vector (LLVM.IntW 64) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨51, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration + 64)) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨25, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms ⟨i.val+8, by omega⟩).length iteration)).map PoisonOr.value := by
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val+8])) = _
    simp only [Vector.map_ofFn, Vector.getElem_ofFn, Function.comp_def]
  have h72 : W ⟨119, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  change (Vector.ofFn fun i : Fin 8 => LLVM.add
    ((show Vector (LLVM.IntW 64) 8 from W ⟨25, rfl⟩)[i])
    ((show Vector (LLVM.IntW 64) 8 from W ⟨119, rfl⟩)[i]))[lane.val] = _
  simp only [h0, h72, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn,
    LLVM.Ty.dense]
  simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]

theorem size_hi_lane (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨40, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 32 (AgaveBatchControl.blockSize (ms ⟨lane.val+8, by omega⟩).length
      (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration))) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨25, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms ⟨i.val+8, by omega⟩).length iteration)).map PoisonOr.value := by
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val+8])) = _
    simp only [Vector.map_ofFn, Vector.getElem_ofFn, Function.comp_def]
  have h24 : W ⟨26, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length).map PoisonOr.value := by rfl
  have h72 : W ⟨119, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  change (vtrunc 32 (vumin (Vector.ofFn fun i : Fin 8 => LLVM.sub
    ((show Vector (LLVM.IntW 64) 8 from W ⟨26, rfl⟩)[i])
    ((show Vector (LLVM.IntW 64) 8 from W ⟨25, rfl⟩)[i]))
    (W ⟨119, rfl⟩)) {nsw := true, nuw := true})[lane.val] = _
  simp only [h0, h24, h72, vtrunc, vumin, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_ofFn, LLVM.Ty.dense]
  change LLVM.trunc 32 (umin
    (LLVM.sub (.value (BitVec.ofNat 64 (ms ⟨lane.val+8, by omega⟩).length))
      (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration)))) (.value 64#64))
    {nsw := true, nuw := true} = _
  have hoff : batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration ≤ (ms ⟨lane.val+8, by omega⟩).length := by
    have := AgaveBatchControl.rootIndex_bounds (ms ⟨lane.val+8, by omega⟩).length
    have := Nat.min_le_right iteration (AgaveBatchControl.rootIndex (ms ⟨lane.val+8, by omega⟩).length)
    unfold batchOffset
    omega
  rw [header_size _ _ (hms _) hoff]
  exact truncate_block_size _ (Nat.min_le_right ..)

theorem flags_hi_lane (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨46, rfl⟩)[lane.val] =
    .value (BitVec.ofNat 32 (AgaveBatchControl.blockFlags (ms ⟨lane.val+8, by omega⟩).length
      (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration))) := by
  let W := represented s src len out sched panic ms iteration
  have h0 : W ⟨25, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (batchOffset (ms ⟨i.val+8, by omega⟩).length iteration)).map PoisonOr.value := by
    change (Vector.ofFn fun i : Fin 8 => PoisonOr.value ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val+8])) = _
    simp only [Vector.map_ofFn, Vector.getElem_ofFn, Function.comp_def]
  have h24 : W ⟨26, rfl⟩ = (Vector.ofFn fun i : Fin 8 =>
      BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length).map PoisonOr.value := by rfl
  have h72 : W ⟨119, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64] := by rfl
  have h73 : W ⟨128, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 64)) [0] := by rfl
  have h70 : W ⟨117, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 32)) [0] := by rfl
  have h69 : W ⟨116, rfl⟩ = LLVM.Ty.dense (.vector 8 (.bitvec 32)) [10] := by rfl
  change (Vector.ofFn fun i : Fin 8 => LLVM.or
    ((vselect ((vicmp .ugt (W ⟨26, rfl⟩)
      (Vector.ofFn fun j : Fin 8 => LLVM.add
        ((show Vector (LLVM.IntW 64) 8 from W ⟨25, rfl⟩)[j])
        ((show Vector (LLVM.IntW 64) 8 from W ⟨119, rfl⟩)[j]))))
      (W ⟨117, rfl⟩) (W ⟨116, rfl⟩))[i])
    ((vzext 32 (vicmp .eq (W ⟨25, rfl⟩) (W ⟨128, rfl⟩)))[i])
    {«disjoint» := true})[lane.val] = _
  simp only [h0, h24, h72, h73, h70, h69, vicmp, vselect, vzext,
    Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, LLVM.Ty.dense]
  change LLVM.or (LLVM.select ((LLVM.icmp .ugt
    (.value (BitVec.ofNat 64 (ms ⟨lane.val+8, by omega⟩).length))
    (LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration))) (.value 64#64))))
    (.value 0#32) (.value 10#32))
    (LLVM.zext 32 (LLVM.icmp .eq (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration)))
      (.value 0#64))) {«disjoint» := true} = _
  have hadd : LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration)))
      (.value 64#64) = .value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration + 64)) := by
    simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]
  rw [hadd, batchOffset_llvm_active _ _ (hms _)]
  have hoff := batchOffset_le_960 (ms ⟨lane.val+8, by omega⟩).length iteration (hms _)
  have heq : LLVM.icmp .eq (.value (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration)))
      (.value 0#64) = .value (BitVec.ofBool (decide (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration = 0))) := by
    have hm : batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration % 18446744073709551616 =
      batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration := Nat.mod_eq_of_lt (by omega)
    simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind]
    by_cases hz : batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration = 0
    · simp [hz]
    · have hb : BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration) ≠ 0#64 := by
        intro hb
        have ht := congrArg BitVec.toNat hb
        simp only [BitVec.toNat_ofNat] at ht
        omega
      have hbeq : (BitVec.ofNat 64 (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hb
      simp [hz, hbeq]
  rw [heq]
  change LLVM.or (LLVM.select (.value (BitVec.ofBool (decide (iteration < AgaveBatchControl.rootIndex (ms ⟨lane.val+8, by omega⟩).length))))
    (.value 0#32) (.value 10#32))
    (LLVM.zext 32 (.value (BitVec.ofBool (decide (batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration = 0)))))
    {«disjoint» := true} = _
  rw [header_flags]
  have ha := AgaveBatchControl.active_iff_before_root (ms ⟨lane.val+8, by omega⟩).length iteration
  change (¬(ms ⟨lane.val+8, by omega⟩).length ≤ batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration + 64 ↔
    iteration < AgaveBatchControl.rootIndex (ms ⟨lane.val+8, by omega⟩).length) at ha
  congr 2
  unfold AgaveBatchControl.blockFlags
  by_cases ha' : iteration < AgaveBatchControl.rootIndex (ms ⟨lane.val+8, by omega⟩).length
  · have hn : ¬ (ms ⟨lane.val+8, by omega⟩).length ≤ batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration + 64 := ha.mpr ha'
    simp [ha', hn]
  · have hn : (ms ⟨lane.val+8, by omega⟩).length ≤ batchOffset (ms ⟨lane.val+8, by omega⟩).length iteration + 64 := by omega
    simp [ha', hn]



/-- Little-endian packing used by the compiler's joined flag/length halves. -/
def packWords16 (v : Fin 16 → BitVec 32) : Vector (BitVec 64) 8 :=
  Vector.ofFn fun i => v ⟨2*i.val+1, by omega⟩ ++ v ⟨2*i.val, by omega⟩

private theorem vector_defined {n w : Nat} (v : Vector (BitVec w) n) :
    LLVM.Ty.Defined (.vector n (.bitvec (.concrete w))) (v.map PoisonOr.value) := by
  intro i
  show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
  rw [Vector.getElem_map]
  exact PoisonOr.value_ne_poison _

private theorem packBits_eq_packLanes {n w : Nat} (v : Vector (BitVec w) n) :
    packBits v = BitVec.packLanes v := by
  unfold packBits LLVM.Ty.flattenBV
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  change ((v.map PoisonOr.value)[i]).toOption.getD 0 = v[i]
  rw [Vector.getElem_map]
  rfl

private theorem assoc32 {n : Nat} (x : BitVec n) (y z : BitVec 32) :
    (x ++ y) ++ z = x ++ (y ++ z) := BitVec.append_assoc

theorem packBits_packWords16 (v : Fin 16 → BitVec 32) :
    packBits (packWords16 v) = packBits (Vector.ofFn v) := by
  rw [packBits_eq_packLanes, packBits_eq_packLanes]
  simp only [packWords16]
  simp [BitVec.packLanes, Vector.tail_ofFn, Vector.getElem_ofFn, Fin.succ,
    -Vector.tail_eq_cast_extract]
  simp only [assoc32]

theorem words16_packWords16 (v : Fin 16 → BitVec 32) :
    BatchPaths16.words16 ((packWords16 v).map PoisonOr.value) =
      (Vector.ofFn v).map PoisonOr.value := by
  change bitcast (.vector 8 (.bitvec (.concrete 64)))
    (.vector 16 (.bitvec (.concrete 32))) ((packWords16 v).map PoisonOr.value) = _
  rw [bitcast_of_defined (vector_defined (packWords16 v))]
  change LLVM.Ty.unflatten (.vector 16 (.bitvec (.concrete 32)))
    (packBits (n := 8) (w := 64) (packWords16 v)) = _
  rw [packBits_packWords16]
  exact unflatten_packBits _

private theorem bitcast32_packCV8 (v : Fin 8 → BitVec 32) :
    bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64)))
      ((Vector.ofFn v).map PoisonOr.value) = (packCV8 v).map PoisonOr.value := by
  rw [bitcast_of_defined (vector_defined (Vector.ofFn v))]
  change LLVM.Ty.unflatten (.vector 4 (.bitvec (.concrete 64)))
    (packBits (n := 8) (w := 32) (Vector.ofFn v)) = _
  rw [← BatchUpdate.packBits_packCV8]
  exact unflatten_packBits _

private def join64 (lo hi : Vector (LLVM.IntW 64) 4)
    (filler : Vector (LLVM.IntW 64) 4) : Vector (LLVM.IntW 64) 8 :=
  LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) [0, 1, 2, 3, 12, 13, 14, 15]
    (LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 1, 2, 3, -1, -1, -1, -1] lo filler)
    (LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [-1, -1, -1, -1, 0, 1, 2, 3] hi filler)

private theorem shuffleLane {l : Nat} (mask : List Int)
    (a b : Vector (LLVM.IntW 64) l) (i : Nat) (hi : i < mask.length) :
    (LLVM.Ty.shufflevector (e := .bitvec (.concrete 64)) mask a b)[i] =
      (let m := mask.getD i (-1)
       if m < 0 then .poison
       else if h : m.toNat < l then a[m.toNat]
       else if h : m.toNat - l < l then b[m.toNat - l] else .poison) := by
  simp only [LLVM.Ty.shufflevector, Vector.getElem_ofFn]
  rfl

private theorem join64_eq (lo hi filler : Vector (LLVM.IntW 64) 4) :
    join64 lo hi filler = lo ++ hi := by
  apply Vector.ext
  intro i h
  change i < 8 at h
  interval_cases i <;>
    simp only [join64] <;>
    repeat' (rw [shuffleLane]; simp only [↓reduceIte, ↓reduceDIte,
      List.getD_cons_zero, List.getD_cons_succ, Int.reduceLT, Int.reduceToNat,
      Nat.reduceLT, Nat.reduceSub, List.length_cons, List.length_nil, Nat.reduceAdd])
  all_goals rw [Vector.getElem_append]; rfl

private theorem pack_halves (v : Fin 16 → BitVec 32) :
    ((packCV8 fun i => v ⟨i.val, by omega⟩).map PoisonOr.value) ++
      ((packCV8 fun i => v ⟨i.val+8, by omega⟩).map PoisonOr.value) =
      (packWords16 v).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_append]
  interval_cases i <;> simp [packCV8, packWords16]

/-- The exact shuffle/bitcast network joining the two flag halves. -/
theorem flags_packing (V : Input16.Valuation) :
    (show Vector (LLVM.IntW 64) 8 from values16 V ⟨43, rfl⟩) =
      join64
        (bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64)))
          (values16 V ⟨61, rfl⟩))
        (bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64)))
          (values16 V ⟨46, rfl⟩)) (V ⟨115, rfl⟩) := by rfl

/-- The exact shuffle/bitcast network joining the two block-length halves. -/
theorem size_packing (V : Input16.Valuation) :
    (show Vector (LLVM.IntW 64) 8 from values16 V ⟨37, rfl⟩) =
      join64
        (bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64)))
          (values16 V ⟨56, rfl⟩))
        (bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 4 (.bitvec (.concrete 64)))
          (values16 V ⟨40, rfl⟩)) (V ⟨115, rfl⟩) := by rfl

attribute [local irreducible] values16

/-- The actual packed size register agrees with all sixteen scalar lanes. -/
theorem size_packed (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 64) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨37, rfl⟩) =
    (packWords16 fun lane => BitVec.ofNat 32 (AgaveBatchControl.blockSize (ms lane).length
      (batchOffset (ms lane).length iteration))).map PoisonOr.value := by
  rw [size_packing, join64_eq]
  have hlo : (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨56, rfl⟩) =
      (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 32 (AgaveBatchControl.blockSize
        (ms ⟨i.val, by omega⟩).length
        (batchOffset (ms ⟨i.val, by omega⟩).length iteration))).map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    simpa only [Vector.getElem_map, Vector.getElem_ofFn] using
      size_lo_lane s src len out sched panic ms iteration ⟨i, hi⟩ hms
  have hhi : (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨40, rfl⟩) =
      (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 32 (AgaveBatchControl.blockSize
        (ms ⟨i.val+8, by omega⟩).length
        (batchOffset (ms ⟨i.val+8, by omega⟩).length iteration))).map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    simpa only [Vector.getElem_map, Vector.getElem_ofFn] using
      size_hi_lane s src len out sched panic ms iteration ⟨i, hi⟩ hms
  dsimp only at hlo hhi
  rw [hlo, hhi, bitcast32_packCV8, bitcast32_packCV8]
  exact pack_halves (fun lane => BitVec.ofNat 32 (AgaveBatchControl.blockSize (ms lane).length
      (batchOffset (ms lane).length iteration)))

/-- Reinterpreting the compiled packed size yields the model's sixteen u32 lanes. -/
theorem size_words16 (hms : ∀ i, (ms i).length ≤ 1024) :
    BatchPaths16.words16 (values16
      (represented s src len out sched panic ms iteration) ⟨37, rfl⟩) =
    (Vector.ofFn fun lane => BitVec.ofNat 32 (AgaveBatchControl.blockSize (ms lane).length
      (batchOffset (ms lane).length iteration))).map PoisonOr.value := by
  exact (congrArg BatchPaths16.words16
    (size_packed s src len out sched panic ms iteration hms)).trans (words16_packWords16 _)

/-- The actual packed flags register agrees with all sixteen scalar lanes. -/
theorem flags_packed (hms : ∀ i, (ms i).length ≤ 1024) :
    (show Vector (LLVM.IntW 64) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨43, rfl⟩) =
    (packWords16 fun lane => BitVec.ofNat 32 (AgaveBatchControl.blockFlags (ms lane).length
      (batchOffset (ms lane).length iteration))).map PoisonOr.value := by
  rw [flags_packing, join64_eq]
  have hlo : (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨61, rfl⟩) =
      (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 32 (AgaveBatchControl.blockFlags
        (ms ⟨i.val, by omega⟩).length
        (batchOffset (ms ⟨i.val, by omega⟩).length iteration))).map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    simpa only [Vector.getElem_map, Vector.getElem_ofFn] using
      flags_lo_lane s src len out sched panic ms iteration ⟨i, hi⟩ hms
  have hhi : (show Vector (LLVM.IntW 32) 8 from values16
      (represented s src len out sched panic ms iteration) ⟨46, rfl⟩) =
      (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 32 (AgaveBatchControl.blockFlags
        (ms ⟨i.val+8, by omega⟩).length
        (batchOffset (ms ⟨i.val+8, by omega⟩).length iteration))).map PoisonOr.value := by
    apply Vector.ext
    intro i hi
    simpa only [Vector.getElem_map, Vector.getElem_ofFn] using
      flags_hi_lane s src len out sched panic ms iteration ⟨i, hi⟩ hms
  dsimp only at hlo hhi
  rw [hlo, hhi, bitcast32_packCV8, bitcast32_packCV8]
  exact pack_halves (fun lane => BitVec.ofNat 32 (AgaveBatchControl.blockFlags (ms lane).length
      (batchOffset (ms lane).length iteration)))

/-- Reinterpreting the compiled packed flags yields the model's sixteen u32 lanes. -/
theorem flags_words16 (hms : ∀ i, (ms i).length ≤ 1024) :
    BatchPaths16.words16 (values16
      (represented s src len out sched panic ms iteration) ⟨43, rfl⟩) =
    (Vector.ofFn fun lane => BitVec.ofNat 32 (AgaveBatchControl.blockFlags (ms lane).length
      (batchOffset (ms lane).length iteration))).map PoisonOr.value := by
  exact (congrArg BatchPaths16.words16
    (flags_packed s src len out sched panic ms iteration hms)).trans (words16_packWords16 _)

end AgaveLatticeHash.MLIR.BatchHeader16
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.advanced_lo_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.size_lo_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.flags_lo_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.advanced_hi_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.size_hi_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.flags_hi_lane
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.packBits_packWords16
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.words16_packWords16
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.flags_packing
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.size_packing
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.size_packed
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.flags_packed
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.size_words16
#print axioms AgaveLatticeHash.MLIR.BatchHeader16.flags_words16

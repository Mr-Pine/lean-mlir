/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeader16Mask

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Frozen active bytes at the represented scalar-prefix state. -/
def activeBytes16 (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : Vector (BitVec 8) 16 :=
  Vector.ofFn fun lane => if iteration < AgaveBatchControl.rootIndex (ms lane).length then 1#8 else 0#8

private theorem half_active (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (f : Fin 8 → Fin 16) (j : Fin 8) (hms : ∀ lane, (ms lane).length ≤ 1024) :
    (BatchHeader16Mask.halfBytes
      (Vector.ofFn fun i => PoisonOr.value (BitVec.ofNat 64 (ms (f i)).length))
      (Vector.ofFn fun i => PoisonOr.value (BitVec.ofNat 64 (batchOffset (ms (f i)).length iteration)))
      (LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64]))[j.val] =
    PoisonOr.value (if iteration < AgaveBatchControl.rootIndex (ms (f j)).length then 1#8 else 0#8) := by
  simp only [BatchHeader16Mask.halfBytes, vzext, vicmp, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_ofFn, LLVM.Ty.dense]
  change LLVM.freeze (LLVM.zext 8 (LLVM.icmp .ugt
    (.value (BitVec.ofNat 64 (ms (f j)).length))
    (LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms (f j)).length iteration))) (.value 64#64)))) = _
  have hadd : LLVM.add (.value (BitVec.ofNat 64 (batchOffset (ms (f j)).length iteration)))
      (.value 64#64) = .value (BitVec.ofNat 64 (batchOffset (ms (f j)).length iteration + 64)) := by
    simp [LLVM.add, LLVM.add?, BitVec.ofNat_add]
  rw [hadd, batchOffset_llvm_active _ _ (hms _)]
  by_cases h : iteration < AgaveBatchControl.rootIndex (ms (f j)).length <;>
    simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The actual header's byte mask agrees lane-for-lane with scalar activity. -/
theorem header_active_bytes16 (s : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    (show Vector (LLVM.IntW 8) 16 from BatchHeader16.values16
      (headerAt16Val (BatchEntry16.entryVal16 s src len out sched panic
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length)
        (Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length))
        ms iteration) ⟨33, rfl⟩) =
      (activeBytes16 ms iteration).map PoisonOr.value := by
  rw [BatchHeader16Mask.active_bytes]
  change (show Vector (LLVM.IntW 8) 16 from (BatchHeader16Mask.halfBytes
      ((Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val, by omega⟩).length).map PoisonOr.value)
      (Vector.ofFn fun i : Fin 8 => PoisonOr.value
        ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val]))
      (LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64])) ++
    (BatchHeader16Mask.halfBytes
      ((Vector.ofFn fun i : Fin 8 => BitVec.ofNat 64 (ms ⟨i.val+8, by omega⟩).length).map PoisonOr.value)
      (Vector.ofFn fun i : Fin 8 => PoisonOr.value
        ((Vector.ofFn fun lane : Fin 16 => BitVec.ofNat 64 (batchOffset (ms lane).length iteration))[i.val+8]))
      (LLVM.Ty.dense (.vector 8 (.bitvec 64)) [64]))) =
      (activeBytes16 ms iteration).map PoisonOr.value
  simp only [Vector.map_ofFn, Vector.getElem_ofFn]
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_append]
  split
  · simpa only [activeBytes16, Vector.getElem_map, Vector.getElem_ofFn,
      Function.comp_def] using
      half_active ms iteration (fun i => ⟨i.val, by omega⟩) ⟨i, by omega⟩ hms
  · have hidx : i - 8 + 8 = i := by omega
    simpa only [activeBytes16, Vector.getElem_map, Vector.getElem_ofFn,
      Function.comp_def, hidx] using
      half_active ms iteration (fun i => ⟨i.val+8, by omega⟩) ⟨i-8, by omega⟩ hms

end AgaveLatticeHash.MLIR

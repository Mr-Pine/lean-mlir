/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchProof
import SSA.Projects.Agave.LatticeHash.MLIR.Memory

set_option maxHeartbeats 1000000

namespace AgaveLatticeHash.MLIR.BatchUpdate
open LeanMLIR SLLVM
open InstCombine (LLVM)

def bytes32 (v : Vector (BitVec 32) 8) : Vector (BitVec 8) 32 :=
  Vector.ofFn fun i => v[i.val / 4]'(by omega) |>.extractLsb' (8 * (i.val % 4)) 8

private theorem extract_extract {n : Nat} (x : BitVec n) (start len i w : Nat)
    (h : i + w ≤ len) :
    (x.extractLsb' start len).extractLsb' i w = x.extractLsb' (start+i) w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  have hji : i + j < len := by omega
  simp [hj, hji, Nat.add_assoc]

private theorem packBits_byte (v : Vector (BitVec 32) 8) (i : Fin 32) :
    (packBits v).extractLsb' (i.val * 8) 8 = (bytes32 v)[i] := by
  simp only [Fin.getElem_fin, bytes32, Vector.getElem_ofFn]
  have he := extract_extract (packBits v) ((i.val/4)*32) 32 (8*(i.val%4)) 8 (by omega)
  have hn : (i.val/4)*32 + 8*(i.val%4) = i.val*8 := by omega
  simp only [hn] at he
  refine he.symm.trans ?_
  simpa only [Fin.getElem_fin] using congrArg (fun x : BitVec 32 => x.extractLsb' (8*(i.val%4)) 8)
    (extract_packBits v ⟨i.val/4, by omega⟩)

theorem bitcast32_bytes (v : Vector (BitVec 32) 8) :
    bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8)))
      (v.map PoisonOr.value) = (bytes32 v).map PoisonOr.value := by
  rw [bitcast_of_defined]
  · apply Vector.ext
    intro i hi
    simp only [LLVM.Ty.unflatten, LLVM.Ty.width, BitVec.setWidth_eq,
      Vector.getElem_ofFn, Vector.getElem_map]
    change PoisonOr.value ((packBits v).extractLsb' (i * 8) 8) = _
    rw [packBits_byte v ⟨i, hi⟩]
    rfl
  · intro i
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

/-- Packing adjacent u32 SIMD lanes into u64 lanes preserves every byte. -/
theorem packBits_packCV8 (v : Fin 8 → BitVec 32) :
    packBits (packCV8 v) = packBits (Vector.ofFn v) := by
  rw [packBits_eq_packLanes, packBits_eq_packLanes]
  simp only [packCV8]
  simp [BitVec.packLanes, Vector.tail_ofFn, Vector.getElem_ofFn, Fin.succ,
    -Vector.tail_eq_cast_extract]
  simp only [assoc32]

private theorem bits_eq_of_bytes (a b : BitVec 256)
    (h : ∀ i : Fin 32, a.extractLsb' (i.val * 8) 8 = b.extractLsb' (i.val * 8) 8) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have he := congrArg (fun x : BitVec 8 => x.getLsbD (j%8)) (h ⟨j/8, by omega⟩)
  have hn : j/8*8+j%8=j := by omega
  simpa only [BitVec.getLsbD_extractLsb', show j%8<8 by omega, decide_true,
    Bool.true_and, hn] using he

theorem packBits_bytes32 (v : Vector (BitVec 32) 8) : packBits (bytes32 v) = packBits v := by
  apply bits_eq_of_bytes
  intro i
  exact (extract_packBits (bytes32 v) i).trans (packBits_byte v i).symm

private theorem vector_defined {n w : Nat} (v : Vector (BitVec w) n) :
    LLVM.Ty.Defined (.vector n (.bitvec (.concrete w))) (v.map PoisonOr.value) := by
  intro i
  show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
  rw [Vector.getElem_map]
  exact PoisonOr.value_ne_poison _

theorem bitcast64_bytes (v : Fin 8 → BitVec 32) :
    bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8)))
      ((packCV8 v).map PoisonOr.value) = (bytes32 (Vector.ofFn v)).map PoisonOr.value := by
  rw [bitcast_of_defined (vector_defined _)]
  change LLVM.Ty.unflatten (.vector 32 (.bitvec (.concrete 8))) (packBits (n := 4) (w := 64) (packCV8 v)) = _
  rw [packBits_packCV8]
  exact (bitcast_of_defined (vector_defined (Vector.ofFn v))).symm.trans (bitcast32_bytes _)

theorem bitcast_bytes64 (v : Fin 8 → BitVec 32) :
    bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64)))
      ((bytes32 (Vector.ofFn v)).map PoisonOr.value) = (packCV8 v).map PoisonOr.value := by
  rw [bitcast_of_defined (vector_defined _)]
  change LLVM.Ty.unflatten (.vector 4 (.bitvec (.concrete 64))) (packBits (n := 32) (w := 8) (bytes32 (Vector.ofFn v))) = _
  rw [packBits_bytes32, ← packBits_packCV8]
  exact unflatten_packBits _

def active8 (active : Fin 8 → Bool) : Vector (LLVM.IntW 1) 8 :=
  Vector.ofFn fun i => .value (BitVec.ofBool (active i))
def maskBytes (active : Fin 8 → Bool) : Vector (LLVM.IntW 1) 32 :=
  Vector.ofFn fun i => .value (BitVec.ofBool (active ⟨i.val/4, by omega⟩))
def signWords (active : Fin 8 → Bool) : Vector (BitVec 32) 8 :=
  Vector.ofFn fun i => if active i then -1 else 0

theorem sext_active8 (active : Fin 8 → Bool) :
    vsext 32 (active8 active) = (signWords active).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [vsext, active8, signWords, Vector.getElem_map, Vector.getElem_ofFn]
  cases h : active ⟨i, hi⟩ <;> rfl

theorem maskBytes_eq (active : Fin 8 → Bool) :
    vicmp .slt
      (bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8)))
        (vsext 32 (active8 active)))
      (Vector.replicate 32 (.value 0#8)) = maskBytes active := by
  rw [sext_active8, bitcast32_bytes]
  apply Vector.ext
  intro i hi
  simp only [vicmp, maskBytes, Vector.getElem_ofFn, Vector.getElem_replicate,
    Fin.getElem_fin, Vector.getElem_map, bytes32, signWords]
  have hm : i%4 < 4 := by omega
  interval_cases hmod : i%4 <;>
    cases h : active ⟨i/4, by omega⟩ <;>
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.slt, BitVec.toInt_eq_toNat_cond]

/-- Selecting four bytes with the same lane mask selects that complete u32. -/
theorem select_bytes (active : Fin 8 → Bool) (a b : Fin 8 → BitVec 32) :
    vselect (maskBytes active) ((bytes32 (Vector.ofFn a)).map PoisonOr.value)
      ((bytes32 (Vector.ofFn b)).map PoisonOr.value) =
      (bytes32 (Vector.ofFn fun i => if active i then a i else b i)).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [vselect, maskBytes, bytes32, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map]
  cases h : active ⟨i/4, by omega⟩ <;> simp [LLVM.select]

/-- The compiler's sext/byte-compare/select/repack sequence is lane-wise CV selection. -/
theorem maskedCV_eq (active : Fin 8 → Bool) (new old : Fin 8 → BitVec 32) :
    bitcast (.vector 32 (.bitvec (.concrete 8))) (.vector 4 (.bitvec (.concrete 64)))
      (vselect
        (vicmp .slt
          (bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8)))
            (vsext 32 (active8 active)))
          (Vector.replicate 32 (.value 0#8)))
        (bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 8)))
          ((Vector.ofFn new).map PoisonOr.value))
        (bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 32 (.bitvec (.concrete 8)))
          ((packCV8 old).map PoisonOr.value))) =
      (packCV8 (fun i => if active i then new i else old i)).map PoisonOr.value := by
  rw [maskBytes_eq, bitcast32_bytes, bitcast64_bytes, select_bytes, bitcast_bytes64]

end AgaveLatticeHash.MLIR.BatchUpdate

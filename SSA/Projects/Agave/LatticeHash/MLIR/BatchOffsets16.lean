/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.Memory

namespace AgaveLatticeHash.MLIR.BatchUpdate16
open LeanMLIR SLLVM
open InstCombine (LLVM)
set_option maxHeartbeats 1200000

/-- The loop bound proves both overflow promises on emitted offset additions. -/
theorem add64_safe (offset : BitVec 64) (h : offset.toNat ≤ 960) :
    LLVM.add (.value offset) (.value 64#64) {nsw := true, nuw := true} =
      PoisonOr.value (offset + 64) := by
  have hi : offset.toInt = (offset.toNat : Int) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : offset.saddOverflow 64#64 = false := by
    simp only [BitVec.saddOverflow, hi]
    norm_num
    omega
  have hu : offset.uaddOverflow 64#64 = false := by
    simp only [BitVec.uaddOverflow]
    norm_num
    omega
  simp [LLVM.add, LLVM.add?, hs, hu]

def activeBytes16 (active : Fin 16 → Bool) : Vector (LLVM.IntW 8) 16 :=
  Vector.ofFn fun i => .value ((BitVec.ofBool (active i)).zeroExtend 8)

theorem trunc_active (active : Bool) :
    LLVM.trunc 1 (.value ((BitVec.ofBool active).zeroExtend 8)) {nsw := false, nuw := true} =
      PoisonOr.value (BitVec.ofBool active) := by cases active <;> rfl

theorem extract_active (active : Fin 16 → Bool) (i : Fin 16) :
    LLVM.Ty.extractelement (e := .bitvec (.concrete 8)) (activeBytes16 active)
      (.value (BitVec.ofNat 64 i.val)) =
      PoisonOr.value ((BitVec.ofBool (active i)).zeroExtend 8) := by
  have hn : (BitVec.ofNat 64 i.val).toNat = i.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  simp [LLVM.Ty.extractelement, hn, i.isLt, activeBytes16]

private theorem extract_extract {n : Nat} (x : BitVec n) (start len i w : Nat)
    (h : i + w ≤ len) :
    (x.extractLsb' start len).extractLsb' i w = x.extractLsb' (start+i) w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  have hji : i + j < len := by omega
  simp [hj, hji, Nat.add_assoc]

/-- The emitted bitcast/extract pair reads the low bit of an active byte. -/
theorem active_bit (active : Fin 16 → Bool) (i : Fin 16) :
    LLVM.Ty.extractelement (e := .bitvec (.concrete 1))
      (bitcast (.vector 16 (.bitvec (.concrete 8))) (.vector 128 (.bitvec (.concrete 1)))
        (activeBytes16 active)) (.value (BitVec.ofNat 64 (8*i.val))) =
      PoisonOr.value (BitVec.ofBool (active i)) := by
  let bytes : Vector (BitVec 8) 16 := Vector.ofFn fun j => (BitVec.ofBool (active j)).zeroExtend 8
  have hb : activeBytes16 active = bytes.map PoisonOr.value := by
    apply Vector.ext; intro j hj; simp [activeBytes16, bytes]
  rw [hb, bitcast_of_defined]
  · have hn : (BitVec.ofNat 64 (8*i.val)).toNat = 8*i.val := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
    simp only [LLVM.Ty.extractelement, hn, show 8*i.val < 128 by omega, dite_true,
      LLVM.Ty.unflatten, LLVM.Ty.width, BitVec.setWidth_eq, Vector.getElem_ofFn,
      Nat.mul_one]
    change PoisonOr.value ((packBits bytes).extractLsb' (8*i.val) 1) = _
    have he := extract_extract (packBits bytes) (i.val*8) 8 0 1 (by omega)
    simp only [Nat.add_zero] at he
    rw [Nat.mul_comm 8 i.val, ← he, extract_packBits]
    simp only [bytes, Fin.getElem_fin, Vector.getElem_ofFn]
    cases active i <;> rfl
  · intro j
    show LLVM.Ty.ofBitvec ((bytes.map PoisonOr.value)[j.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _

/-- A scalar-controlled vector selection after insertion updates only that lane. -/
theorem select_insert (v : Vector (LLVM.IntW 64) 8) (x : LLVM.IntW 64)
    (i : Fin 8) (active : Bool) :
    vselectScalar (.value (BitVec.ofBool active))
      (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) v x
        (.value (BitVec.ofNat 64 i.val))) v =
      v.set i.val (LLVM.select (.value (BitVec.ofBool active)) x v[i]) := by
  have hn : (BitVec.ofNat 64 i.val).toNat = i.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  simp only [LLVM.Ty.insertelement, hn, i.isLt, dite_true]
  apply Vector.ext
  intro j hj
  simp only [vselectScalar, Vector.getElem_ofFn, Vector.getElem_set, Fin.getElem_fin]
  by_cases he : i.val = j
  · subst j; cases active <;> simp [LLVM.select]
  · cases active <;> simp [LLVM.select, he]

theorem select_value (active : Bool) (a b : BitVec w) :
    LLVM.select (.value (BitVec.ofBool active)) (.value a) (.value b) =
      PoisonOr.value (if active then a else b) := by cases active <;> rfl

def updateHalf (old fresh : Vector (BitVec 64) 8) (active : Fin 8 → Bool) :
    Vector (LLVM.IntW 64) 8 :=
  let step (v : Vector (LLVM.IntW 64) 8) (i : Fin 8) :=
    vselectScalar (.value (BitVec.ofBool (active i)))
      (LLVM.Ty.insertelement (e := .bitvec (.concrete 64)) v (.value fresh[i])
        (.value (BitVec.ofNat 64 i.val))) v
  let v0 := step (old.map PoisonOr.value) 0
  let v1 := step v0 1
  let v2 := step v1 2
  let v3 := step v2 3
  let v4 := step v3 4
  let v5 := step v4 5
  let v6 := step v5 6
  step v6 7

/-- Eight emitted scalar-select insertions equal one lane-wise masked update. -/
theorem updateHalf_eq (old fresh : Vector (BitVec 64) 8) (active : Fin 8 → Bool) :
    updateHalf old fresh active =
      Vector.ofFn (fun i => PoisonOr.value (if active i then fresh[i] else old[i])) := by
  simp only [updateHalf, select_insert]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Vector.getElem_set, select_value]

end AgaveLatticeHash.MLIR.BatchUpdate16

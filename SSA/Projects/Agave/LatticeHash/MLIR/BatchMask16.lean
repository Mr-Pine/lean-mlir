import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.Primitives

namespace AgaveLatticeHash.MLIR.BatchMask16
open LeanMLIR SLLVM
open InstCombine (LLVM)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- The exact scalar active-mask network emitted in %2119 through %2174. -/
def packMaskWord16 (bytes : Vector (LLVM.IntW 8) 16) : LLVM.IntW 16 :=
  let v0 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 0)
  let v1 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 1)
  let v2 := LLVM.shl v1 (.value 1) {nsw := true, nuw := true}
  let v3 := LLVM.or v2 v0 {«disjoint» := true}
  let v4 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 2)
  let v5 := LLVM.shl v4 (.value 2) {nsw := true, nuw := true}
  let v6 := LLVM.or v5 v3 {«disjoint» := true}
  let v7 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 3)
  let v8 := LLVM.shl v7 (.value 3) {nsw := true, nuw := true}
  let v9 := LLVM.or v8 v6 {«disjoint» := true}
  let v10 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 4)
  let v11 := LLVM.shl v10 (.value 4) {nsw := true, nuw := true}
  let v12 := LLVM.or v11 v9 {«disjoint» := true}
  let v13 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 5)
  let v14 := LLVM.shl v13 (.value 5) {nsw := true, nuw := true}
  let v15 := LLVM.or v14 v12
  let v16 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 6)
  let v17 := LLVM.shl v16 (.value 6) {nsw := true, nuw := true}
  let v18 := LLVM.or v17 v15
  let v19 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 7)
  let v20 := LLVM.shl v19 (.value 7) {nsw := false, nuw := true}
  let v21 := LLVM.or v20 v18
  let v22 := LLVM.zext 16 v21
  let v23 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 8)
  let v24 := LLVM.zext 16 v23 {«nneg» := true}
  let v25 := LLVM.shl v24 (.value 8) {nsw := true, nuw := true}
  let v26 := LLVM.or v25 v22 {«disjoint» := true}
  let v27 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 9)
  let v28 := LLVM.zext 16 v27 {«nneg» := true}
  let v29 := LLVM.shl v28 (.value 9) {nsw := true, nuw := true}
  let v30 := LLVM.or v29 v26 {«disjoint» := true}
  let v31 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 10)
  let v32 := LLVM.zext 16 v31 {«nneg» := true}
  let v33 := LLVM.shl v32 (.value 10) {nsw := true, nuw := true}
  let v34 := LLVM.or v33 v30 {«disjoint» := true}
  let v35 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 11)
  let v36 := LLVM.zext 16 v35 {«nneg» := true}
  let v37 := LLVM.shl v36 (.value 11) {nsw := true, nuw := true}
  let v38 := LLVM.or v37 v34
  let v39 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 12)
  let v40 := LLVM.zext 16 v39 {«nneg» := true}
  let v41 := LLVM.shl v40 (.value 12) {nsw := true, nuw := true}
  let v42 := LLVM.or v41 v38
  let v43 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 13)
  let v44 := LLVM.zext 16 v43 {«nneg» := true}
  let v45 := LLVM.shl v44 (.value 13) {nsw := true, nuw := true}
  let v46 := LLVM.or v45 v42
  let v47 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 14)
  let v48 := LLVM.zext 16 v47 {«nneg» := true}
  let v49 := LLVM.shl v48 (.value 14) {nsw := true, nuw := true}
  let v50 := LLVM.or v49 v46
  let v51 := LLVM.Ty.extractelement (w := 64) (l := 16) (e := .bitvec (.concrete 8)) bytes (.value 15)
  let v52 := LLVM.zext 16 v51 {«nneg» := true}
  let v53 := LLVM.shl v52 (.value 15) {nsw := false, nuw := true}
  let v54 := LLVM.or v53 v50
  v54

def packMask16 (bytes : Vector (LLVM.IntW 8) 16) : Vector (LLVM.IntW 1) 16 :=
  bitcast (.bitvec (.concrete 16)) (.vector 16 (.bitvec (.concrete 1))) (packMaskWord16 bytes)

private theorem shift_8_1 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 8)) (.value 1)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 8) <<< 1) := by
  cases b <;> rfl

private theorem shift_8_2 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 8)) (.value 2)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 8) <<< 2) := by
  cases b <;> rfl

private theorem shift_8_3 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 8)) (.value 3)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 8) <<< 3) := by
  cases b <;> rfl

private theorem shift_8_4 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 8)) (.value 4)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 8) <<< 4) := by
  cases b <;> rfl

private theorem shift_8_5 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 8)) (.value 5)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 8) <<< 5) := by
  cases b <;> rfl

private theorem shift_8_6 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 8)) (.value 6)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 8) <<< 6) := by
  cases b <;> rfl

private theorem shift_8_7 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 8)) (.value 7)
      {nsw := false, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 8) <<< 7) := by
  cases b <;> rfl

private theorem shift_16_8 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 8)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 8) := by
  cases b <;> rfl

private theorem shift_16_9 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 9)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 9) := by
  cases b <;> rfl

private theorem shift_16_10 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 10)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 10) := by
  cases b <;> rfl

private theorem shift_16_11 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 11)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 11) := by
  cases b <;> rfl

private theorem shift_16_12 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 12)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 12) := by
  cases b <;> rfl

private theorem shift_16_13 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 13)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 13) := by
  cases b <;> rfl

private theorem shift_16_14 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 14)
      {nsw := true, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 14) := by
  cases b <;> rfl

private theorem shift_16_15 (b : Bool) :
    LLVM.shl (.value ((BitVec.ofBool b).zeroExtend 16)) (.value 15)
      {nsw := false, nuw := true} =
    .value (((BitVec.ofBool b).zeroExtend 16) <<< 15) := by
  cases b <;> rfl

private theorem zext_bit (b : Bool) :
    LLVM.zext 16 (.value ((BitVec.ofBool b).zeroExtend 8)) {«nneg» := true} =
    .value ((BitVec.ofBool b).zeroExtend 16) := by
  cases b <;> rfl

private theorem or_defined {w : Nat} (x y : BitVec w) (flag : LLVM.DisjointFlag)
    (h : x &&& y = 0) : LLVM.or (.value x) (.value y) flag = .value (x ||| y) := by
  simp [LLVM.or, LLVM.or?, h]

theorem packMaskWord16_exact (active : BitVec 16) :
    packMaskWord16 (Vector.ofFn fun i : Fin 16 =>
      .value ((BitVec.ofBool (active.getLsbD i.val)).zeroExtend 8)) = .value active := by
  unfold packMaskWord16
  simp only [LLVM.Ty.extractelement, BitVec.reduceToNat,
    Nat.reduceLT, ↓reduceDIte, Vector.getElem_ofFn]
  rw [shift_8_1]
  rw [shift_8_2]
  rw [shift_8_3]
  rw [shift_8_4]
  rw [shift_8_5]
  rw [shift_8_6]
  rw [shift_8_7]
  simp only [zext_bit]
  rw [shift_16_8]
  rw [shift_16_9]
  rw [shift_16_10]
  rw [shift_16_11]
  rw [shift_16_12]
  rw [shift_16_13]
  rw [shift_16_14]
  rw [shift_16_15]
  repeat rw [or_defined _ _ _ (by (apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp))]
  simp only [LLVM.zext, LLVM.zext?, PoisonOr.value_bind, Bool.false_eq_true, false_and, ↓reduceIte]
  repeat rw [or_defined _ _ _ (by (apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp))]
  congr 1
  (apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp)

/-- Every lane of the emitted scalar network is the original active bit;
this includes the `nsw`, `nuw`, `nneg`, and disjoint-OR poison checks. -/
theorem packMask16_exact (active : Fin 16 → Bool) :
    packMask16 (Vector.ofFn fun i =>
      .value ((BitVec.ofBool (active i)).zeroExtend 8)) =
    Vector.ofFn (fun i => .value (BitVec.ofBool (active i))) := by
  let bits : Vector (BitVec 1) 16 := Vector.ofFn fun i => BitVec.ofBool (active i)
  have hb (i : Fin 16) : (packBits bits).getLsbD i.val = active i := by
    have he := congrArg (fun b : BitVec 1 => b.getLsbD 0) (extract_packBits bits i)
    simpa [BitVec.getLsbD_extractLsb', bits] using he
  have hw := packMaskWord16_exact (packBits bits)
  simp only [hb] at hw
  unfold packMask16
  rw [hw]
  rw [bitcast_of_defined]
  · apply Vector.ext
    intro i hi
    simp only [LLVM.Ty.unflatten, LLVM.Ty.width, BitVec.setWidth_eq,
      Vector.getElem_ofFn]
    change PoisonOr.value ((packBits bits).extractLsb' (i * 1) 1) = _
    rw [extract_packBits bits ⟨i, hi⟩]
    simp [bits]
  · exact PoisonOr.value_ne_poison _

end AgaveLatticeHash.MLIR.BatchMask16


#print axioms AgaveLatticeHash.MLIR.BatchMask16.packMask16_exact

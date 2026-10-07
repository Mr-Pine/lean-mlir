import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScaleScalar
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMultiplication

namespace Agave.Ed25519.Tables.Avx2Constructor.CacheScale
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases Avx2SquareNegateD
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def replicateWord (n : Nat) : ⟦Ty.vec 4 64⟧ := Vector.replicate 4 (natWord n)
def wideVec (z : Fin 4 → Nat) : V64 := Vector.ofFn (fun lane => BitVec.ofNat 64 (z lane))

def reductionInstructions (z : Fin 10 → ⟦Ty.vec 4 64⟧) : Fin 10 → ⟦Ty.vec 4 64⟧ :=
  let v550 := z 0
  let v551 := z 1
  let v552 := z 2
  let v553 := z 3
  let v554 := z 4
  let v555 := z 5
  let v556 := z 6
  let v557 := z 7
  let v558 := z 8
  let v559 := z 9
  let v560 := Vector.zipWith (Operation.lshr false) v550 (replicateWord 26)
  let v561 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v560 v551
  let v562 := Vector.zipWith Operation.and v550 (replicateWord 67108862)
  let v563 := Vector.zipWith (Operation.lshr false) v554 (replicateWord 26)
  let v564 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v563 v555
  let v565 := Vector.zipWith Operation.and v554 (replicateWord 67108862)
  let v566 := Vector.zipWith (Operation.lshr false) v561 (replicateWord 25)
  let v567 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v566 v552
  let v568 := Vector.zipWith Operation.and v561 (replicateWord 33554431)
  let v569 := Vector.zipWith (Operation.lshr false) v564 (replicateWord 25)
  let v570 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v569 v556
  let v571 := Vector.zipWith Operation.and v564 (replicateWord 33554431)
  let v572 := Vector.zipWith (Operation.lshr false) v567 (replicateWord 26)
  let v573 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v572 v553
  let v574 := Vector.zipWith (Operation.lshr false) v570 (replicateWord 26)
  let v575 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v574 v557
  let v576 := Vector.zipWith (Operation.lshr false) v573 (replicateWord 25)
  let v577 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v576 v565
  let v578 := Vector.zipWith (Operation.lshr false) v575 (replicateWord 25)
  let v579 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v578 v558
  let v580 := Vector.zipWith (Operation.lshr false) v577 (replicateWord 26)
  let v581 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v580 v571
  let v582 := Vector.zipWith (Operation.lshr false) v579 (replicateWord 26)
  let v583 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v582 v559
  let v584 := Vector.zipWith (Operation.lshr false) v583 (replicateWord 25)
  let v585 := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v584 (replicateWord 19)
  let v586 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v585 v562
  let v587 := Vector.zipWith (Operation.lshr false) v586 (replicateWord 26)
  let v588 := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v587 v568
  ![v586, v588, v567, v573, v577, v581, v570, v575, v579, v583]

theorem reductionInstructions_lane (z : Fin 10 → ⟦Ty.vec 4 64⟧)
    (i : Fin 10) (lane : Fin 4) :
    (reductionInstructions z i)[lane] = scalarInstructions (fun j => (z j)[lane]) i := by
  fin_cases i <;> simp [reductionInstructions, scalarInstructions, replicateWord]

theorem reductionInstructions_nat (z : Fin 10 → Fin 4 → Nat)
    (hz : ∀ i lane, z i lane < 2^50) (he : ∀ i lane, z i lane % 2 = 0) (i : Fin 10) :
    reductionInstructions (fun j => Ty.wrap (t := .vec 4 64) (wideVec (z j))) i =
      Ty.wrap (wideVec (fun lane => scalarNat (fun j => z j lane) i)) := by
  apply Vector.ext
  intro lane hlane
  have hs := congrFun (scalarInstructions_nat (fun j => z j ⟨lane, hlane⟩)
    (fun j => hz j _) (fun j => he j _)) i
  change (reductionInstructions _ i)[(⟨lane, hlane⟩ : Fin 4)] = _
  rw [reductionInstructions_lane]
  simpa [wideVec, Ty.wrap_vec, natWord] using hs

def scaleConstant : Fin 4 → Nat := ![121666,121666,243332,243330]
def scaledPoint (P : Point) : Point :=
  ⟨CacheArithmetic.scaleReduce 121666 P.X, CacheArithmetic.scaleReduce 121666 P.Y,
   CacheArithmetic.scaleReduce 243332 P.Z, CacheArithmetic.scaleReduce 243330 P.T⟩
def scaledColumns (P : Point) : Fin 10 → Fin 4 → Nat :=
  fun i lane => scaleConstant lane * coordinate P lane i

theorem scaledColumns_bound {P : Point} (hP : pointWide P) (i : Fin 10) (lane : Fin 4) :
    scaledColumns P i lane < 2^50 := by
  have h := pointWide_coordinate hP lane i
  have hc : scaleConstant lane ≤ 243332 := by fin_cases lane <;> decide
  have hm := Nat.mul_le_mul hc h
  unfold scaledColumns
  unfold wideCap at hm
  split_ifs at hm <;> norm_num at hm ⊢ <;> omega

theorem scaledColumns_even (P : Point) (i : Fin 10) (lane : Fin 4) :
    scaledColumns P i lane % 2 = 0 := by
  fin_cases lane <;> simp [scaledColumns, scaleConstant, Nat.mul_mod]

theorem scaledPoint_reduced {P : Point} (hP : pointWide P) : pointReduced (scaledPoint P) := by
  exact ⟨CacheArithmetic.scaleReduce_reduced _ (by decide) hP.1,
    CacheArithmetic.scaleReduce_reduced _ (by decide) hP.2.1,
    CacheArithmetic.scaleReduce_reduced _ (by decide) hP.2.2.1,
    CacheArithmetic.scaleReduce_reduced _ (by decide) hP.2.2.2⟩

def widenInstructions (x : Fin 5 → ⟦Ty.vec 8 32⟧) : Fin 10 → ⟦Ty.vec 4 64⟧ := ![
  Operation.bitcast (by decide) (Operation.shufflevector evenMask (x 0) evenZeros),
  Operation.bitcast (by decide) (Operation.shufflevector oddMask (x 0) oddZeros),
  Operation.bitcast (by decide) (Operation.shufflevector evenMask (x 1) evenZeros),
  Operation.bitcast (by decide) (Operation.shufflevector oddMask (x 1) oddZeros),
  Operation.bitcast (by decide) (Operation.shufflevector evenMask (x 2) evenZeros),
  Operation.bitcast (by decide) (Operation.shufflevector oddMask (x 2) oddZeros),
  Operation.bitcast (by decide) (Operation.shufflevector evenMask (x 3) evenZeros),
  Operation.bitcast (by decide) (Operation.shufflevector oddMask (x 3) oddZeros),
  Operation.bitcast (by decide) (Operation.shufflevector evenMask (x 4) evenZeros),
  Operation.bitcast (by decide) (Operation.shufflevector oddMask (x 4) oddZeros)]

def scaleInstructions (x : Fin 5 → ⟦Ty.vec 8 32⟧) : Fin 10 → ⟦Ty.vec 4 64⟧ :=
  fun i => Vector.zipWith (Operation.mul {nsw := true, nuw := true})
    (widenInstructions x i) (Ty.wrap (t := .vec 4 64) (wideVec scaleConstant))

theorem wide_ofNat (a : Nat) (ha : a < 2^32) :
    (BitVec.ofNat 32 a).setWidth 64 = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem wide_coordinate {P : Point} (hP : pointWide P) (lane : Fin 4) (i : Fin 10) :
    coordinate P lane i < 2^32 := by
  have h := (wide_input_safety (pointWide_coordinate hP lane) i).1
  omega

theorem widenInstructions_point {P : Point} (hP : pointWide P) (i : Fin 10) :
    widenInstructions (fun k => Ty.wrap (t := .vec 8 32) (packPoint P k)) i =
      Ty.wrap (wideVec (fun lane => coordinate P lane i)) := by
  have hw (lane : Fin 4) (j : Fin 10) := wide_ofNat _ (wide_coordinate hP lane j)
  fin_cases i <;>
    simp only [widenInstructions, Matrix.cons_val_zero, Matrix.cons_val_succ,
      unpack_even_instructions, unpack_odd_instructions]
  all_goals apply Vector.ext
  all_goals intro lane hlane
  all_goals interval_cases lane <;>
    simp [packPoint, evenIndex, oddIndex, unpackEven, unpackOdd, wideVec,
      Ty.wrap_vec, word, coordinate] at hw ⊢
  all_goals first | exact hw 0 _ | exact hw 1 _ | exact hw 2 _ | exact hw 3 _

theorem scaleInstructions_point {P : Point} (hP : pointWide P) (i : Fin 10) :
    scaleInstructions (fun k => Ty.wrap (t := .vec 8 32) (packPoint P k)) i =
      Ty.wrap (wideVec (scaledColumns P i)) := by
  rw [scaleInstructions, widenInstructions_point hP]
  apply Vector.ext
  intro lane hlane
  have hc : scaleConstant ⟨lane, hlane⟩ ≤ 243332 := by
    interval_cases lane <;> norm_num [scaleConstant]
  have ha := wide_coordinate hP ⟨lane, hlane⟩ i
  have hm := scaledColumns_bound hP i ⟨lane, hlane⟩
  have hmul := mul_nat (coordinate P ⟨lane, hlane⟩ i) (scaleConstant ⟨lane, hlane⟩)
    (by omega) (by omega) (by simpa only [scaledColumns, Nat.mul_comm] using
      (show scaledColumns P i ⟨lane, hlane⟩ < 2^63 by omega))
  simpa only [Vector.getElem_zipWith, Ty.wrap_vec, Vector.getElem_map, wideVec,
    Vector.getElem_ofFn, natWord, scaledColumns, Nat.mul_comm] using hmul

end Agave.Ed25519.Tables.Avx2Constructor.CacheScale

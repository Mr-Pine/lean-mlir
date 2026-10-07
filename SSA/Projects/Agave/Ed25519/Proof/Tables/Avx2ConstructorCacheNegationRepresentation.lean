import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheNegationCarry
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorNormalizationRepresentation

namespace Agave.Ed25519.Tables.Avx2Constructor.CacheNegation
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases CacheArithmetic
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def negativePoint (Q : Point) : Point :=
  ⟨negateColumns Q.X, negateColumns Q.Y, negateColumns Q.Z, negateColumns Q.T⟩

def resultPoint (Q : Point) : Point := ⟨Q.X,Q.Y,Q.Z,negateReduce Q.T⟩

def constants (k : Fin 5) : V32 :=
  let a := word (sixteenP (evenIndex k))
  let b := word (sixteenP (oddIndex k))
  #v[a,a,b,b,a,a,b,b]

def subtract (flagged : Bool) (x : ⟦Ty.vec 8 32⟧) (k : Fin 5) : ⟦Ty.vec 8 32⟧ :=
  Vector.zipWith (Operation.sub {nsw := flagged, nuw := flagged}) (Ty.wrap (t := .vec 8 32) (constants k)) x

def blend (x y : ⟦Ty.vec 8 32⟧) : ⟦Ty.vec 8 32⟧ :=
  Operation.shufflevector #v[some 0,some 1,some 2,some 3,some 4,some 13,some 6,some 15] x y

def instructions (B : Fin 5 → ⟦Ty.vec 8 32⟧) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  let n : Fin 5 → ⟦Ty.vec 8 32⟧ := fun k => subtract (k.val != 0) (B k) k
  ![blend (B 0) (Vector.zipWith (Operation.add {nsw := true, nuw := true})
      (firstInstructions (n 0)) (foldInstructions (n 4))),
    blend (B 1) (stepInstructions (n 0) (n 1)),
    blend (B 2) (stepInstructions (n 1) (n 2)),
    blend (B 3) (stepInstructions (n 2) (n 3)),
    blend (B 4) (stepInstructions (n 3) (n 4))]

theorem subtract_point (flagged : Bool) {Q : Point} (hQ : pointReduced Q) (k : Fin 5) :
    subtract flagged (Ty.wrap (packPoint Q k)) k = Ty.wrap (packPoint (negativePoint Q) k) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [subtract, constants, packPoint, negativePoint, Ty.wrap_vec,
    sub_word flagged hQ.1, sub_word flagged hQ.2.1,
    sub_word flagged hQ.2.2.1, sub_word flagged hQ.2.2.2]

theorem top_eq_normalization (x : BitVec 32) (hx : x.toNat < 2^29) :
    top x = Normalization.top x := by
  apply BitVec.eq_of_toNat_eq
  rw [top_exact x hx, Normalization.top_toNat]

theorem negative_last_bound (a : Avx2FieldMul.Limbs) :
    (word (negateColumns a 9)).toNat < 2^29 := by
  have h := negateColumns_bound a 9
  norm_num [radix] at h
  exact (Nat.mod_le _ _).trans_lt h

theorem carry_high_small (x y : BitVec 32) :
    ((x >>> 26)+(y &&& 33554431#32)).toNat < 2^28 := by
  have hx := Normalization.shift_small x 26 (Or.inr rfl)
  have hx' : (x >>> 26).toNat < 64 := by
    have h := x.isLt
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num at h ⊢; omega
  have hy : (y &&& 33554431#32).toNat < 2^25 := by
    rw [BitVec.toNat_and]
    have h : y.toNat &&& 33554431 ≤ 33554431 := Nat.and_le_right
    norm_num; omega
  rw [BitVec.toNat_add]
  exact (Nat.mod_le _ _).trans_lt (by norm_num at hy ⊢; omega)

theorem top_mul_small (x : BitVec 32) : (top x * 19).toNat < 2^28 := by
  have h := top_bound x
  rw [BitVec.toNat_mul]
  exact (Nat.mod_le _ _).trans_lt (by norm_num; omega)

theorem add_first_value (x y : V32) :
    Vector.zipWith (Operation.add {nsw := true, nuw := true})
      (firstInstructions (Ty.wrap x)) (foldInstructions (Ty.wrap y)) =
      pair ((x[5] &&& 67108863#32) + top y[7]*19)
        ((x[5] >>> 26)+(x[7] &&& 33554431#32)) := by
  rw [first_value, fold_value]
  have hlo := Normalization.add_small (x[5] &&& 67108863#32) (top y[7]*19#32)
    (mask32_small _ _ (by decide)) (top_mul_small _)
  have hhi := Normalization.add_small ((x[5] >>> 26)+(x[7] &&& 33554431#32)) 0#32
    (carry_high_small _ _) (by decide)
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [pair, hlo, hhi]
  all_goals rfl

theorem negative_word_toNat (a : Avx2FieldMul.Limbs) (i : Fin 10) :
    (word (negateColumns a i)).toNat = negateColumns a i := by
  have h := negateColumns_bound a i
  unfold radix at h
  apply Nat.mod_eq_of_lt
  split_ifs at h <;> norm_num at h ⊢ <;> omega

theorem mask26_toNat (x : BitVec 32) : (x &&& 67108863#32).toNat = x.toNat % 2^26 := by
  change x.toNat &&& (2^26-1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem mask25_toNat (x : BitVec 32) : (x &&& 33554431#32).toNat = x.toNat % 2^25 := by
  change x.toNat &&& (2^25-1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem carry26_word (x y : BitVec 32) :
    (x >>> 25)+(y &&& 67108863#32) = word (y.toNat % 2^26 + x.toNat / 2^25) := by
  apply BitVec.eq_of_toNat_eq
  simp only [word, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, mask26_toNat, Nat.add_comm]

theorem carry25_word (x y : BitVec 32) :
    (x >>> 26)+(y &&& 33554431#32) = word (y.toNat % 2^25 + x.toNat / 2^26) := by
  apply BitVec.eq_of_toNat_eq
  simp only [word, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, mask25_toNat, Nat.add_comm]

theorem first_word (x y : BitVec 32) (hx : x.toNat < 2^29) :
    (y &&& 67108863#32)+top x*19#32 = word (y.toNat % 2^26 + 19*(x.toNat / 2^25)) := by
  rw [top_eq_normalization x hx, Normalization.first_word, mask26_toNat]

/-- The exact partial-lane carry network negates only the D coordinate and
leaves the other three physical coordinates intact. -/
theorem instructions_point {Q : Point} (hQ : pointReduced Q) (k : Fin 5) :
    instructions (fun j => Ty.wrap (packPoint Q j)) k =
      Ty.wrap (packPoint (resultPoint Q) k) := by
  unfold instructions
  simp only [subtract_point _ hQ]
  have hf := add_first_value (packPoint (negativePoint Q) 0) (packPoint (negativePoint Q) 4)
  fin_cases k <;> dsimp only
  all_goals simp only [hf, step_value]
  all_goals apply Vector.ext
  all_goals intro i hi
  all_goals interval_cases i <;> simp [blend, pair, packPoint, negativePoint,
    resultPoint, negateReduce, carry32, evenIndex, oddIndex, Ty.wrap_vec,
    carry26_word, carry25_word, first_word _ _ (negative_last_bound Q.T), negative_word_toNat]

end Agave.Ed25519.Tables.Avx2Constructor.CacheNegation

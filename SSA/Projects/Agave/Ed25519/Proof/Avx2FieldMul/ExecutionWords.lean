import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.WordProduct

/-! The scalar word interface for executing the AVX2 convolution.  It retains
the two narrowing operations performed by the source: doubling the selected
left u32 limb and taking the low u32 of `19 * right`.  The caller-derived
asymmetric bounds suffice to identify this with `wordColumn`. -/

namespace Agave.Ed25519.Avx2FieldMul.Execution

abbrev RawLimbs := Fin 10 → BitVec 32

def rawTerm (a b : RawLimbs) (i j : Fin 10) : BitVec 64 :=
  (if i.val % 2 = 1 ∧ j.val % 2 = 1 then a i <<< 1 else a i).setWidth 64 *
    (if 10 ≤ i.val + j.val then ((b j).setWidth 64 * 19#64).setWidth 32
      else b j).setWidth 64

def rawColumn (a b : RawLimbs) (k : Fin 10) : BitVec 64 :=
  sum10 fun i => rawTerm a b i (rhsIndex k i)

def rawProduct (a b : RawLimbs) : Fin 10 → BitVec 64 :=
  Reduce64.Word.reduce (rawColumn a b)

theorem left_wide_exact {x : Limbs} (hx : LeftBound x) (i : Fin 10) :
    (BitVec.ofNat 32 (x i)).setWidth 64 = BitVec.ofNat 64 (x i) := by
  have h := asymmetric_doubled_lt_u32 hx i
  exact BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64) (by decide) (by omega)

theorem right_wide_exact {y : Limbs} (hy : RightBound y) (i : Fin 10) :
    (BitVec.ofNat 32 (y i)).setWidth 64 = BitVec.ofNat 64 (y i) := by
  have h := asymmetric_scaled_rhs_lt_u32 hy i
  exact BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64) (by decide) (by omega)

theorem left_twice_exact {x : Limbs} (hx : LeftBound x) (i : Fin 10) :
    (BitVec.ofNat 32 (x i) <<< 1).setWidth 64 =
      BitVec.ofNat 64 (2 * x i) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change (BitVec.ofNat 32 (x i) * BitVec.ofNat 32 2).setWidth 64 = _
  rw [← BitVec.ofNat_mul]
  have h : x i * 2 < 2^32 := by
    simpa [Nat.mul_comm] using asymmetric_doubled_lt_u32 hx i
  rw [BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64) (by decide) h, Nat.mul_comm]

theorem right_times19_exact {y : Limbs} (hy : RightBound y) (i : Fin 10) :
    (((BitVec.ofNat 32 (y i)).setWidth 64 * 19#64).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 (19 * y i) := by
  rw [right_wide_exact hy]
  change ((BitVec.ofNat 64 (y i) * BitVec.ofNat 64 19).setWidth 32).setWidth 64 = _
  rw [← BitVec.ofNat_mul, BitVec.setWidth_ofNat_of_le (w := 64) (v := 32) (by decide)]
  have h : y i * 19 < 2^32 := by
    simpa [Nat.mul_comm] using asymmetric_scaled_rhs_lt_u32 hy i
  rw [BitVec.setWidth_ofNat_of_le_of_lt (w := 32) (v := 64) (by decide) h, Nat.mul_comm]

/-- The integer product is obtained from the actual split factors, with both
narrowing operations justified by the original caller bounds. -/
theorem rawTerm_ofNat {x y : Limbs} (hx : LeftBound x) (hy : RightBound y)
    (i j : Fin 10) :
    rawTerm (fun k => BitVec.ofNat 32 (x k)) (fun k => BitVec.ofNat 32 (y k)) i j =
      BitVec.ofNat 64 (term x y i j) := by
  have hl :
      (if i.val % 2 = 1 ∧ j.val % 2 = 1 then BitVec.ofNat 32 (x i) <<< 1
        else BitVec.ofNat 32 (x i)).setWidth 64 =
      BitVec.ofNat 64 ((if i.val % 2 = 1 ∧ j.val % 2 = 1 then 2 else 1) * x i) := by
    split_ifs
    · exact left_twice_exact hx i
    · simpa using left_wide_exact hx i
  have hr :
      (if 10 ≤ i.val + j.val then
          ((BitVec.ofNat 32 (y j)).setWidth 64 * 19#64).setWidth 32
        else BitVec.ofNat 32 (y j)).setWidth 64 =
      BitVec.ofNat 64 ((if 10 ≤ i.val + j.val then 19 else 1) * y j) := by
    split_ifs
    · exact right_times19_exact hy j
    · simpa using right_wide_exact hy j
  unfold rawTerm
  rw [hl, hr, ← BitVec.ofNat_mul, split_scaled_term]

theorem rawColumn_eq_wordColumn {x y : Limbs} (hx : LeftBound x) (hy : RightBound y)
    (k : Fin 10) :
    rawColumn (fun i => BitVec.ofNat 32 (x i)) (fun i => BitVec.ofNat 32 (y i)) k =
      wordColumn x y k := by
  unfold rawColumn wordColumn
  congr 1
  funext i
  rw [rawTerm_ofNat hx hy]
  simp only [← BitVec.ofNat_mul, term]

theorem rawProduct_eq_wordProduct {x y : Limbs} (hx : LeftBound x) (hy : RightBound y) :
    rawProduct (fun i => BitVec.ofNat 32 (x i)) (fun i => BitVec.ofNat 32 (y i)) =
      wordProduct x y := by
  have hcolumns :
      rawColumn (fun i => BitVec.ofNat 32 (x i)) (fun i => BitVec.ofNat 32 (y i)) =
        wordColumn x y := funext (rawColumn_eq_wordColumn hx hy)
  exact congrArg Reduce64.Word.reduce hcolumns

theorem rawProduct_toNat {x y : Limbs} (hx : LeftBound x) (hy : RightBound y)
    (i : Fin 10) :
    (rawProduct (fun k => BitVec.ofNat 32 (x k))
      (fun k => BitVec.ofNat 32 (y k)) i).toNat = product x y i := by
  rw [rawProduct_eq_wordProduct hx hy]
  exact wordProduct_toNat hx hy i

end Agave.Ed25519.Avx2FieldMul.Execution

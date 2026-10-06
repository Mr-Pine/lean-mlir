import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Asymmetric

/-! Word-level arithmetic contract for the AVX2 convolution. `sum10` has the
same grouping as Rust's helper. The RIR execution bridge must additionally
identify the shuffled/widened inputs with these mathematical limbs. -/
namespace Agave.Ed25519.Avx2FieldMul

/-- Exactly the parenthesization of Rust's `sum10`, including its last add. -/
def sum10 {α : Type} [Add α] (x : Fin 10 → α) : α :=
  ((x 0 + x 1) + (x 2 + x 3)) +
    ((x 4 + x 5) + (x 6 + x 7)) + (x 8 + x 9)

theorem sum10_nat (x : Limbs) : sum10 x = ∑ i, x i := by
  have hten : (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by
    ext i
    fin_cases i <;> decide
  rw [hten]
  simp [sum10, Nat.add_assoc]

theorem sum10_ofNat (x : Limbs) :
    sum10 (fun i => BitVec.ofNat 64 (x i)) = BitVec.ofNat 64 (sum10 x) := by
  simp only [sum10, ← BitVec.ofNat_add]

theorem sum10_toNat (x : Limbs) (h : (∑ i, x i) < 2 ^ 64) :
    (sum10 (fun i => BitVec.ofNat 64 (x i))).toNat = ∑ i, x i := by
  rw [sum10_ofNat, BitVec.toNat_ofNat, sum10_nat, Nat.mod_eq_of_lt h]

/-- Machine-width convolution after unpacking and exact u32 pre-scaling.
This definition does not include the shuffle, memory, or carry instructions. -/
def wordColumn (x y : Limbs) (k : Fin 10) : BitVec 64 :=
  sum10 (fun i => BitVec.ofNat 64 (coefficient i (rhsIndex k i)) *
    BitVec.ofNat 64 (x i) * BitVec.ofNat 64 (y (rhsIndex k i)))

/-- The wrapping word computation equals the unbounded convolution under
caller-derived bounds. `partial_column_lt_u64` separately gives every
intermediate addition bound, including when LLVM marks an add `nuw`. -/
theorem wordColumn_toNat {x y : Limbs} (hx : Bounded x) (hy : Bounded y)
    (k : Fin 10) : (wordColumn x y k).toNat = column x y k := by
  have h : column x y k < 2 ^ 64 := by
    have h := column_bound hx hy k
    norm_num at h ⊢
    omega
  unfold wordColumn
  simp only [← BitVec.ofNat_mul]
  exact sum10_toNat (fun i => term x y i (rhsIndex k i)) h

theorem wordColumn_mod {x y : Limbs} (hx : Bounded x) (hy : Bounded y) :
    Field.decode10 (fun k => (wordColumn x y k).toNat) % Field.p =
      (Field.decode10 x * Field.decode10 y) % Field.p := by
  simp only [wordColumn_toNat hx hy]
  exact convolution_mod x y

/-- Word-level convolution is also exact for the larger asymmetric limits. -/
theorem asymmetric_wordColumn_toNat {x y : Limbs}
    (hx : LeftBound x) (hy : RightBound y) (k : Fin 10) :
    (wordColumn x y k).toNat = column x y k := by
  have h : column x y k < 2 ^ 64 := by
    have h := asymmetric_column_lt_i64 hx hy k
    norm_num at h ⊢
    omega
  unfold wordColumn
  simp only [← BitVec.ofNat_mul]
  exact sum10_toNat (fun i => term x y i (rhsIndex k i)) h

end Agave.Ed25519.Avx2FieldMul

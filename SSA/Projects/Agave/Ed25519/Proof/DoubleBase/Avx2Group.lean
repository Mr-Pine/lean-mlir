import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Group

/-!
AVX2's group-valued loop invariant, proved per point operation. No equality
between complete backend results is used: point addition/doubling refinement,
concrete lookup-table certificates, and positional NAF reconstruction suffice.
-/
namespace Agave.Ed25519.DoubleBase
open PointArithmetic Tables

theorem represents_avx2Add {P Q : Extended F} {V W : GroupPoint}
    (hP : Represents P V) (hQ : Represents Q W) :
    Represents (avx2Add P Q) (V + W) :=
  represents_related (represents_serialAdd hP hQ)
    (add_related _root_.Ed25519.d _root_.Ed25519.d_spec (by decide)
      (related_refl P) (related_refl Q))

theorem represents_avx2Double {P : Extended F} {V : GroupPoint}
    (hP : Represents P V) : Represents (avx2Double P) (V + V) := by
  obtain ⟨hP, rfl⟩ := hP
  unfold Represents
  rw [avx2Double_toFD]
  exact ⟨_root_.Ed25519.Point.wellFormed_dbl hP,
    _root_.Ed25519.Point.toAffine_dbl hP⟩

/-- One source sign branch adds the signed digit's group multiple. The only
digit conditions are its actual NAF properties, with a finite table bound. -/
theorem represents_avx2_digitOps (table : TableIndex → Extended F)
    (side : Bool) (V : GroupPoint) (bound : Nat)
    (hTable : ∀ k, k < bound → Represents (table (side, k)) ((2*k+1) • V))
    {P : Extended F} {X : GroupPoint} (hP : Represents P X) (digit : Int)
    (hodd : digit = 0 ∨ digit % 2 = 1) (hbound : digit.natAbs < 2 * bound) :
    Represents ((digitOps side digit).foldl (avx2Step table) P)
      (X + digit • V) := by
  rcases hodd with rfl | hodd
  · simpa [digitOps] using hP
  have hi : digit.natAbs / 2 < bound := by omega
  by_cases hp : 0 < digit
  · have habs := Int.natAbs_of_nonneg (le_of_lt hp)
    have hv : ((2 * (digit.natAbs / 2) + 1 : Nat) : Int) = digit := by omega
    simp only [digitOps, ite_eq_left hp, List.foldl_cons, List.foldl_nil, avx2Step]
    have h := represents_avx2Add hP (hTable _ hi)
    rw [← natCast_zsmul, hv] at h
    exact h
  · have hn : digit < 0 := by omega
    have habs := Int.ofNat_natAbs_of_nonpos (le_of_lt hn)
    have hv : -((2 * (digit.natAbs / 2) + 1 : Nat) : Int) = digit := by omega
    simp only [digitOps, ite_eq_right hp, ite_eq_left hn, List.foldl_cons, List.foldl_nil, avx2Step]
    have h := represents_avx2Add hP (represents_negate (hTable _ hi))
    rw [← natCast_zsmul, ← neg_zsmul, hv] at h
    exact h

theorem avx2_table_A_represents {A : Extended F} {V : GroupPoint}
    (hA : Represents A V) (k : Nat) (hk : k < 8) :
    Represents (finiteTable (avx2DoubleBaseTable A) (false, k)) ((2*k+1) • V) := by
  simpa [finiteTable, hk, avx2DoubleBaseTable, avx2Width5] using
    avx2Odd_represents hA k

theorem avx2_table_B_represents (A : Extended F) (k : Nat) (hk : k < 64) :
    Represents (finiteTable (avx2DoubleBaseTable A) (true, k)) ((2*k+1) • baseGroup) := by
  simpa [finiteTable, hk, avx2DoubleBaseTable] using avx2BasePoint_represents ⟨k, hk⟩

theorem represents_avx2_round_naf {A : Extended F} {V : GroupPoint} (hA : Represents A V)
    (a b i : Nat) {P : Extended F} {X : GroupPoint} (hP : Represents P X) :
    Represents
      ((roundOps (nafDigits 5 a) (nafDigits 8 b) i).foldl
        (avx2Step (finiteTable (avx2DoubleBaseTable A))) P)
      (groupRound V baseGroup X (nafDigits 5 a) (nafDigits 8 b) i) := by
  have h5 := NAF.digits_bounds 5 (Or.inl rfl) 256 0 ⟨a, 0⟩ (by norm_num) i
  have h8 := NAF.digits_bounds 8 (Or.inr rfl) 256 0 ⟨b, 0⟩ (by norm_num) i
  have hi5 := nafDigits_lookup_index_safe 5 (Or.inl rfl) a i
  have hi8 := nafDigits_lookup_index_safe 8 (Or.inr rfl) b i
  norm_num at hi5 hi8
  have hfirst := represents_avx2_digitOps (finiteTable (avx2DoubleBaseTable A)) false V 8
    (avx2_table_A_represents hA) (represents_avx2Double hP) (nafDigits 5 a i)
    h5.2.2 (by omega)
  have hsecond := represents_avx2_digitOps (finiteTable (avx2DoubleBaseTable A)) true baseGroup 64
    (avx2_table_B_represents A) hfirst (nafDigits 8 b i) h8.2.2 (by omega)
  simpa only [roundOps, List.foldl_append, List.foldl_cons, List.foldl_nil,
    avx2Step, groupRound, two_nsmul] using hsecond

/-- Loop invariant: after each high digit, the remaining descending loop has
the exact Horner closed form from that represented intermediate point. -/
theorem represents_avx2_run_naf {A : Extended F} {V : GroupPoint} (hA : Represents A V)
    (a b n : Nat) {P : Extended F} {X : GroupPoint} (hP : Represents P X) :
    Represents
      (run (avx2Step (finiteTable (avx2DoubleBaseTable A)))
        (nafDigits 5 a) (nafDigits 8 b) n P)
      (groupLadder V baseGroup X (nafDigits 5 a) (nafDigits 8 b) n) := by
  induction n generalizing P X with
  | zero =>
    rw [run, groupLadder_zero]
    exact represents_avx2_round_naf hA a b 0 hP
  | succ n ih =>
    rw [run, groupLadder_succ]
    exact ih (represents_avx2_round_naf hA a b (n + 1) hP)

/-- Direct AVX2 group correctness from its own descending-loop invariant. -/
theorem avx2Math_represents_direct {A : Extended F} {V : GroupPoint}
    (hA : Represents A V) (a b : Nat)
    (ha : a < 2 ^ 255) (hb : b < 2 ^ 255) :
    Represents (avx2Math a A b) ((a : Int) • V + (b : Int) • baseGroup) := by
  have h := represents_avx2_run_naf hA a b
    (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) represents_identity
  rw [groupLadder_naf V baseGroup a b ha hb] at h
  exact h

end Agave.Ed25519.DoubleBase

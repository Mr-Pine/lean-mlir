import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Algebra
import Mathlib.Algebra.BigOperators.Intervals

/-! The descending ladder's group value, linked to the existing Firedancer
`Edwards.Point curve` specification. Machine CFG/limb refinement is separate. -/
namespace Agave.Ed25519.DoubleBase

open PointArithmetic Tables Finset
open _root_.Ed25519 (curve)

abbrev GroupPoint := Edwards.Point curve

/-- Closed form of the inclusive ladder from an arbitrary initial point. -/
def groupLadder (A B X : GroupPoint) (a b : Digits) (n : Nat) : GroupPoint :=
  (2 : Nat) ^ (n + 1) • X + ∑ i ∈ range (n + 1),
    ((a i * 2 ^ i) • A + (b i * 2 ^ i) • B)

def groupRound (A B X : GroupPoint) (a b : Digits) (i : Nat) : GroupPoint :=
  (2 : Nat) • X + a i • A + b i • B

theorem groupLadder_zero (A B X : GroupPoint) (a b : Digits) :
    groupLadder A B X a b 0 = groupRound A B X a b 0 := by
  simp [groupLadder, groupRound, add_assoc]

theorem groupLadder_succ (A B X : GroupPoint) (a b : Digits) (n : Nat) :
    groupLadder A B X a b (n + 1) =
      groupLadder A B (groupRound A B X a b (n + 1)) a b n := by
  simp only [groupLadder, groupRound]
  rw [Finset.sum_range_succ _ (n + 1)]
  generalize (∑ i ∈ range (n + 1), ((a i * 2 ^ i) • A + (b i * 2 ^ i) • B)) = S
  rw [smul_add, smul_add, smul_smul, ← pow_succ, mul_smul, mul_smul,
    smul_comm ((2 : Nat) ^ (n + 1)) (a (n + 1)) A,
    smul_comm ((2 : Nat) ^ (n + 1)) (b (n + 1)) B]
  simp only [← natCast_zsmul, Nat.cast_pow, Nat.cast_ofNat]
  abel

theorem groupLadder_skip (A B : GroupPoint) (a b : Digits) :
    groupLadder A B 0 a b (startIndex a b 255) = groupLadder A B 0 a b 255 := by
  let i := startIndex a b 255
  have hi := startIndex_le a b 255
  obtain ⟨j, hj⟩ : ∃ j, 256 = (i + 1) + j := ⟨256 - i - 1, by dsimp [i]; omega⟩
  change groupLadder A B 0 a b i = _
  simp only [groupLadder, smul_zero, zero_add, show 255 + 1 = 256 from rfl, hj,
    Finset.sum_range_add _ _ j, left_eq_add]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hz := skipped_digits_zero a b 255 (i + 1 + x) (by dsimp [i]; omega)
    (by simp only [Finset.mem_range] at hx; omega)
  simp [hz.1, hz.2]

theorem groupLadder_naf (A B : GroupPoint) (a b : Nat)
    (ha : a < 2 ^ 255) (hb : b < 2 ^ 255) :
    groupLadder A B 0 (nafDigits 5 a) (nafDigits 8 b)
      (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) =
        (a : Int) • A + (b : Int) • B := by
  rw [groupLadder_skip]
  simp only [groupLadder, smul_zero, zero_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, nafDigits]
  rw [NAF.sourceDigits_reconstruct 5 (Or.inl rfl) a ha,
    NAF.sourceDigits_reconstruct 8 (Or.inr rfl) b hb]

theorem represents_negate {P : Extended F} {V : GroupPoint} (hP : Represents P V) :
    Represents (negatePoint P) (-V) := by
  obtain ⟨hP, rfl⟩ := hP
  change ∃ h : (toFD P).neg.WellFormed,
    (toFD P).neg.toAffine h = -(toFD P).toAffine hP
  exact ⟨_root_.Ed25519.Point.wellFormed_neg hP, _root_.Ed25519.Point.toAffine_neg hP⟩

theorem represents_identity : Represents (identityPoint : Extended F) (0 : GroupPoint) := by
  refine ⟨_root_.Ed25519.Point.wellFormed_zero, ?_⟩
  exact Edwards.Point.ext (by simp [_root_.Ed25519.Point.toAffine,
    _root_.Ed25519.Point.x, _root_.Ed25519.Point.zero, toFD, identityPoint])
    (by simp [_root_.Ed25519.Point.toAffine, _root_.Ed25519.Point.y,
      _root_.Ed25519.Point.zero, toFD, identityPoint])

theorem represents_projectiveAsExtended {P : Extended F} {V : GroupPoint}
    (hP : Represents P V) : Represents (projectiveAsExtended P) V := by
  have hp := hP.choose
  have hZ : P.Z ≠ 0 := hp.isUnit_Z.ne_zero
  have hXY : P.X * P.Y = P.Z * P.T := by
    have ht := hp.t_spec
    change P.X * P.Y = P.T * P.Z at ht
    simpa [mul_comm] using ht
  apply represents_related hP
  exact ⟨P.Z, hZ, projectiveAsExtended_eq_scale P hXY⟩

/-- One source sign branch adds the signed digit's group multiple. The only
digit conditions are its actual NAF properties, with a finite table bound. -/
theorem represents_digitOps (table : TableIndex → Extended F)
    (side : Bool) (V : GroupPoint) (bound : Nat)
    (hTable : ∀ k, k < bound → Represents (table (side, k)) ((2*k+1) • V))
    {P : Extended F} {X : GroupPoint} (hP : Represents P X) (digit : Int)
    (hodd : digit = 0 ∨ digit % 2 = 1) (hbound : digit.natAbs < 2 * bound) :
    Represents ((digitOps side digit).foldl (serialStep _root_.Ed25519.d table) P)
      (X + digit • V) := by
  rcases hodd with rfl | hodd
  · simpa [digitOps] using hP
  have hi : digit.natAbs / 2 < bound := by omega
  by_cases hp : 0 < digit
  · have habs := Int.natAbs_of_nonneg (le_of_lt hp)
    have hv : ((2 * (digit.natAbs / 2) + 1 : Nat) : Int) = digit := by omega
    simp only [digitOps, if_pos hp, List.foldl_cons, List.foldl_nil, serialStep]
    have h := represents_serialAdd hP (hTable _ hi)
    rw [← natCast_zsmul, hv] at h
    exact h
  · have hn : digit < 0 := by omega
    have habs := Int.ofNat_natAbs_of_nonpos (le_of_lt hn)
    have hv : -((2 * (digit.natAbs / 2) + 1 : Nat) : Int) = digit := by omega
    simp only [digitOps, if_neg hp, if_pos hn, List.foldl_cons, List.foldl_nil, serialStep]
    have h := represents_serialAdd hP (represents_negate (hTable _ hi))
    rw [← natCast_zsmul, ← neg_zsmul, hv] at h
    exact h

theorem serial_table_A_represents {A : Extended F} {V : GroupPoint}
    (hA : Represents A V) (k : Nat) (hk : k < 8) :
    Represents (finiteTable (serialDoubleBaseTable A) (false, k)) ((2*k+1) • V) := by
  simpa [finiteTable, hk, serialDoubleBaseTable, serialWidth5] using
    serialOdd_represents hA k

theorem serial_table_B_represents (A : Extended F) (k : Nat) (hk : k < 64) :
    Represents (finiteTable (serialDoubleBaseTable A) (true, k)) ((2*k+1) • baseGroup) := by
  simpa [finiteTable, hk, serialDoubleBaseTable] using serialBasePoint_represents ⟨k, hk⟩

theorem represents_round_naf {A : Extended F} {V : GroupPoint} (hA : Represents A V)
    (a b i : Nat) {P : Extended F} {X : GroupPoint} (hP : Represents P X) :
    Represents
      ((roundOps (nafDigits 5 a) (nafDigits 8 b) i).foldl
        (serialStep _root_.Ed25519.d (finiteTable (serialDoubleBaseTable A))) P)
      (groupRound V baseGroup X (nafDigits 5 a) (nafDigits 8 b) i) := by
  have h5 := NAF.digits_bounds 5 (Or.inl rfl) 256 0 ⟨a, 0⟩ (by norm_num) i
  have h8 := NAF.digits_bounds 8 (Or.inr rfl) 256 0 ⟨b, 0⟩ (by norm_num) i
  have hi5 := nafDigits_lookup_index_safe 5 (Or.inl rfl) a i
  have hi8 := nafDigits_lookup_index_safe 8 (Or.inr rfl) b i
  norm_num at hi5 hi8
  have hfirst := represents_digitOps (finiteTable (serialDoubleBaseTable A)) false V 8
    (serial_table_A_represents hA) (represents_serialDouble hP) (nafDigits 5 a i)
    h5.2.2 (by omega)
  have hsecond := represents_digitOps (finiteTable (serialDoubleBaseTable A)) true baseGroup 64
    (serial_table_B_represents A) hfirst (nafDigits 8 b i) h8.2.2 (by omega)
  simpa only [roundOps, List.foldl_append, List.foldl_cons, List.foldl_nil,
    serialStep, groupRound, two_nsmul] using hsecond

/-- Loop invariant: after each high digit, the remaining descending loop has
the exact Horner closed form from that represented intermediate point. -/
theorem represents_run_naf {A : Extended F} {V : GroupPoint} (hA : Represents A V)
    (a b n : Nat) {P : Extended F} {X : GroupPoint} (hP : Represents P X) :
    Represents
      (run (serialStep _root_.Ed25519.d (finiteTable (serialDoubleBaseTable A)))
        (nafDigits 5 a) (nafDigits 8 b) n P)
      (groupLadder V baseGroup X (nafDigits 5 a) (nafDigits 8 b) n) := by
  induction n generalizing P X with
  | zero =>
    rw [run, groupLadder_zero]
    exact represents_round_naf hA a b 0 hP
  | succ n ih =>
    rw [run, groupLadder_succ]
    exact ih (represents_round_naf hA a b (n + 1) hP)

/-- The full scalar algebraic implementation computes aA+bB in the same group
used by the existing Firedancer Ed25519 proof. Scalar bounds are the actual
Scalar representation invariant, not assumptions about intermediate values. -/
theorem serialMath_represents {A : Extended F} {V : GroupPoint} (hA : Represents A V)
    (a b : Nat) (ha : a < 2 ^ 255) (hb : b < 2 ^ 255) :
    Represents (serialMath a A b) ((a : Int) • V + (b : Int) • baseGroup) := by
  have h := represents_run_naf hA a b
    (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) represents_identity
  rw [groupLadder_naf V baseGroup a b ha hb] at h
  exact represents_projectiveAsExtended h

/-- The vector algebraic implementation computes precisely the same aA+bB. -/
theorem avx2Math_represents {A : Extended F} {V : GroupPoint} (hA : Represents A V)
    (a b : Nat) (ha : a < 2 ^ 255) (hb : b < 2 ^ 255) :
    Represents (avx2Math a A b) ((a : Int) • V + (b : Int) • baseGroup) := by
  have h := represents_run_naf hA a b
    (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) represents_identity
  rw [groupLadder_naf V baseGroup a b ha hb] at h
  apply represents_related h
  exact double_base_related _root_.Ed25519.d _root_.Ed25519.d_spec (by decide)
    _ _ (finiteTable_related _ _ (doubleBaseTable_related (related_refl A)))
    _ _ (related_refl identityPoint)

end Agave.Ed25519.DoubleBase

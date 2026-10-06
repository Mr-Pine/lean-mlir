import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Integer arithmetic for `FieldElement2625x4::square_and_negate_D` in the
pinned solana-ed25519 0.2.4 source. These lemmas separate the arithmetic
identity and caller bounds from the RIR execution connection.
-/

namespace Agave.Ed25519.Avx2SquareNegateD
section

abbrev Limbs := Fin 10 → Nat
abbrev modulus : Nat := 2^255 - 19

def decode (a : Limbs) : Nat :=
a 0*2^0 +
  a 1*2^26 +
  a 2*2^51 +
  a 3*2^77 +
  a 4*2^102 +
  a 5*2^128 +
  a 6*2^153 +
  a 7*2^179 +
  a 8*2^204 +
  a 9*2^230

theorem decode_add (a b : Limbs) :
    decode (fun i => a i + b i) = decode a + decode b := by
  unfold decode
  ring

/-- Integer columns computed before the D-lane subtraction. -/
def columns (a : Limbs) : Limbs := ![
  1*(a 0*a 0) + 76*(a 1*a 9) + 38*(a 2*a 8) + 76*(a 3*a 7) + 38*(a 4*a 6) + 38*(a 5*a 5),
  2*(a 0*a 1) + 38*(a 2*a 9) + 38*(a 3*a 8) + 38*(a 4*a 7) + 38*(a 5*a 6),
  2*(a 0*a 2) + 2*(a 1*a 1) + 76*(a 3*a 9) + 38*(a 4*a 8) + 76*(a 5*a 7) + 19*(a 6*a 6),
  2*(a 0*a 3) + 2*(a 1*a 2) + 38*(a 4*a 9) + 38*(a 5*a 8) + 38*(a 6*a 7),
  2*(a 0*a 4) + 4*(a 1*a 3) + 1*(a 2*a 2) + 76*(a 5*a 9) + 38*(a 6*a 8) + 38*(a 7*a 7),
  2*(a 0*a 5) + 2*(a 1*a 4) + 2*(a 2*a 3) + 38*(a 6*a 9) + 38*(a 7*a 8),
  2*(a 0*a 6) + 4*(a 1*a 5) + 2*(a 2*a 4) + 2*(a 3*a 3) + 76*(a 7*a 9) + 19*(a 8*a 8),
  2*(a 0*a 7) + 2*(a 1*a 6) + 2*(a 2*a 5) + 2*(a 3*a 4) + 38*(a 8*a 9),
  2*(a 0*a 8) + 4*(a 1*a 7) + 2*(a 2*a 6) + 4*(a 3*a 5) + 1*(a 4*a 4) + 38*(a 9*a 9),
  2*(a 0*a 9) + 2*(a 1*a 8) + 2*(a 2*a 7) + 2*(a 3*a 6) + 2*(a 4*a 5)]

/-- Terms folded across bit 255 during squaring. -/
def high (a : Limbs) : Nat :=
  4*(a 1*a 9)*2^0 +
  2*(a 2*a 8)*2^0 +
  2*(a 2*a 9)*2^26 +
  4*(a 3*a 7)*2^0 +
  2*(a 3*a 8)*2^26 +
  4*(a 3*a 9)*2^51 +
  2*(a 4*a 6)*2^0 +
  2*(a 4*a 7)*2^26 +
  2*(a 4*a 8)*2^51 +
  2*(a 4*a 9)*2^77 +
  2*(a 5*a 5)*2^0 +
  2*(a 5*a 6)*2^26 +
  4*(a 5*a 7)*2^51 +
  2*(a 5*a 8)*2^77 +
  4*(a 5*a 9)*2^102 +
  1*(a 6*a 6)*2^51 +
  2*(a 6*a 7)*2^77 +
  2*(a 6*a 8)*2^102 +
  2*(a 6*a 9)*2^128 +
  2*(a 7*a 7)*2^102 +
  2*(a 7*a 8)*2^128 +
  4*(a 7*a 9)*2^153 +
  1*(a 8*a 8)*2^153 +
  2*(a 8*a 9)*2^179 +
  2*(a 9*a 9)*2^204

theorem columns_identity (a : Limbs) :
    decode (columns a) + modulus * high a = decode a ^ 2 := by
  norm_num [decode, columns, high, modulus]
  ring

theorem columns_mod (a : Limbs) :
    decode (columns a) % modulus = decode a ^ 2 % modulus := by
  have h := congrArg (fun n => n % modulus) (columns_identity a)
  simpa [Nat.add_mod, Nat.mul_mod] using h

/-- Twice the convenient reduced-limb invariant, as used by point doubling:
the D input is X+Y and the other three inputs are individual coordinates. -/
def inputLimit (i : Fin 10) : Nat :=
  if i.val % 2 = 0 then 2*(2^26 + 2^18) else 2*(2^25 + 2^18)

def Bounded (a : Limbs) : Prop := ∀ i, a i ≤ inputLimit i

/-- Every column is monotone in all ten nonnegative coefficients. -/
theorem columns_mono {a b : Limbs} (h : ∀ i, a i ≤ b i) :
    ∀ i, columns a i ≤ columns b i := by
  intro i
  fin_cases i <;> dsimp [columns] <;> gcongr <;> apply h

/-- The exact integer limb of 2^37 times p used for D-lane negation. -/
def negateConstant (i : Fin 10) : Nat :=
  if i = 0 then (2^26-19)*2^37
  else if i.val % 2 = 0 then (2^26-1)*2^37
  else (2^25-1)*2^37

theorem negateConstant_value :
    decode negateConstant = modulus * 2^37 := by
  norm_num [decode, negateConstant, modulus]

/-- Each pre-subtraction square column fits below its subtraction constant.
This excludes both wraparound in the polynomial and D-lane underflow. -/
theorem columns_lt_negateConstant {a : Limbs} (ha : Bounded a) (i : Fin 10) :
    columns a i < negateConstant i := by
  have h := columns_mono ha i
  fin_cases i <;> norm_num [columns, inputLimit, negateConstant] at h ⊢ <;> omega

theorem negateConstant_lt_u63 (i : Fin 10) : negateConstant i < 2^63 := by
  fin_cases i <;> norm_num [negateConstant]

theorem columns_lt_u63 {a : Limbs} (ha : Bounded a) (i : Fin 10) :
    columns a i < 2^63 :=
  lt_trans (columns_lt_negateConstant ha i) (negateConstant_lt_u63 i)

/-- The 32-bit doublings used before unsigned widening multiply do not wrap. -/
theorem input_double_lt_u32 {a : Limbs} (ha : Bounded a) (i : Fin 10) :
    2 * a i < 2^32 := by
  have hi := ha i
  unfold inputLimit at hi
  split_ifs at hi <;> norm_num at hi ⊢ <;> omega

/-- The low-word 19*x multiplication loses no bits under the caller bound. -/
theorem input_times19_lt_u32 {a : Limbs} (ha : Bounded a) (i : Fin 10) :
    19 * a i < 2^32 := by
  have hi := ha i
  unfold inputLimit at hi
  split_ifs at hi <;> norm_num at hi ⊢ <;> omega

/-- Selected mathematical output of the 64-bit blend before reduce64. -/
def signedColumns (a : Limbs) (negate : Bool) : Limbs := fun i =>
  if negate then negateConstant i - columns a i else columns a i

theorem signedColumns_lt_u63 {a : Limbs} (ha : Bounded a)
    (negate : Bool) (i : Fin 10) : signedColumns a negate i < 2^63 := by
  cases negate
  · exact columns_lt_u63 ha i
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (negateConstant_lt_u63 i)

theorem negated_identity {a : Limbs} (ha : Bounded a) :
    decode (signedColumns a true) + decode (columns a) = modulus * 2^37 := by
  rw [← decode_add]
  have h : (fun i => signedColumns a true i + columns a i) = negateConstant := by
    funext i
    exact Nat.sub_add_cancel (Nat.le_of_lt (columns_lt_negateConstant ha i))
  rw [h, negateConstant_value]

/-- The D lane is precisely minus the square in the field. -/
theorem negated_mod {a : Limbs} (ha : Bounded a) :
    (decode (signedColumns a true) + decode a ^ 2) % modulus = 0 := by
  rw [← columns_identity a, ← Nat.add_assoc, negated_identity ha]
  simp [Nat.add_mod, Nat.mul_mod]

/-- An individual coordinate satisfying the maintained slack invariant fits. -/
theorem coordinate_bounded (a : Limbs)
    (h : ∀ i, a i < (if i.val % 2 = 0 then 2^26 else 2^25) + 2^18) :
    Bounded a := by
  intro i
  have hi := h i
  unfold inputLimit
  split_ifs at * <;> omega

/-- The sole enlarged input in point doubling is the limbwise sum X+Y. -/
theorem coordinate_sum_bounded (a b : Limbs)
    (ha : ∀ i, a i < (if i.val % 2 = 0 then 2^26 else 2^25) + 2^18)
    (hb : ∀ i, b i < (if i.val % 2 = 0 then 2^26 else 2^25) + 2^18) :
    Bounded (fun i => a i + b i) := by
  intro i
  have hai := ha i
  have hbi := hb i
  change a i + b i ≤ inputLimit i
  unfold inputLimit
  split_ifs at * <;> omega

end
end Agave.Ed25519.Avx2SquareNegateD

import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Reduced
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Asymmetric

/-! Caller bounds for cached addition. The existing one-bit multiplication
premise is too small for `diff_sum`; the bound below covers both multiplications
in cached add and the single lazy negation in cached subtraction. -/
namespace Agave.Ed25519.Avx2PointAdd
open Avx2FieldMul

def radix (i : Fin 10) : Nat := 2 ^ (if i.val % 2 = 0 then 26 else 25)
def reduced (a : Limbs) : Prop := ∀ i, a i < radix i + 2^18
/-- An integral bound closed over all `diff_sum` outputs. -/
def wideCap (i : Fin 10) : Nat := if i.val % 2 = 0 then 201850880 else 100925440
def wide (a : Limbs) : Prop := ∀ i, a i ≤ wideCap i
/-- The radix-26/25 digits of the exact integer 2p. -/
def twiceP (i : Fin 10) : Nat :=
  if i = 0 then 134217690 else if i.val % 2 = 0 then 134217726 else 67108862

def lazyNeg (a : Limbs) : Limbs := fun i => twiceP i - a i
def lazyDiff (a b : Limbs) : Limbs := fun i => b i + lazyNeg a i
def lazySum (a b : Limbs) : Limbs := fun i => b i + a i

theorem reduced_le_twiceP {a : Limbs} (h : reduced a) (i : Fin 10) :
    a i ≤ twiceP i := by
  have hi := h i
  unfold radix at hi
  unfold twiceP
  split_ifs at hi ⊢ <;> norm_num at * <;> omega

theorem reduced_wide {a : Limbs} (h : reduced a) : wide a := by
  intro i
  have hi := h i
  unfold radix at hi
  unfold wideCap
  split_ifs at hi ⊢ <;> norm_num at * <;> omega

theorem lazyNeg_wide (a : Limbs) : wide (lazyNeg a) := by
  intro i
  have h : twiceP i - a i ≤ twiceP i := Nat.sub_le _ _
  unfold lazyNeg
  unfold twiceP wideCap at *
  split_ifs at * <;> norm_num at * <;> omega

theorem lazyDiff_wide {a b : Limbs} (hb : reduced b) : wide (lazyDiff a b) := by
  intro i
  have hi := hb i
  have hn : twiceP i - a i ≤ twiceP i := Nat.sub_le _ _
  unfold lazyDiff lazyNeg
  unfold radix at hi
  unfold twiceP wideCap at *
  split_ifs at * <;> norm_num at * <;> omega

theorem lazySum_wide {a b : Limbs} (ha : reduced a) (hb : reduced b) :
    wide (lazySum a b) := by
  intro i
  have hai := ha i
  have hbi := hb i
  unfold radix at hai hbi
  unfold lazySum wideCap
  split_ifs at * <;> norm_num at * <;> omega

/-- Neither the lane sums nor the lazy subtraction wrap a u32. -/
theorem preparations_safe {a b : Limbs} (ha : reduced a) (hb : reduced b)
    (i : Fin 10) :
    a i ≤ twiceP i ∧ lazyDiff a b i < 2^32 ∧ lazySum a b i < 2^32 := by
  have hd := lazyDiff_wide (a := a) hb i
  have hs := lazySum_wide ha hb i
  refine ⟨reduced_le_twiceP ha i, ?_, ?_⟩ <;>
    unfold wideCap at hd hs <;> split_ifs at * <;> norm_num at * <;> omega

/-- Every doubled input and every pre-widening multiplication by 19 fits u32. -/
theorem wide_input_safety {a : Limbs} (ha : wide a) (i : Fin 10) :
    2 * a i < 2^32 ∧ 19 * a i < 2^32 := by
  have h := ha i
  unfold wideCap at h
  split_ifs at h <;> norm_num at * <;> omega

/-- The cached-add caller invariant discharges the left premise of the
proved imported AVX2 multiplication helper. -/
theorem wide_left {a : Limbs} (ha : wide a) : LeftBound a := by
  intro i
  have h := ha i
  unfold wideCap at h
  unfold leftLimit
  split_ifs at h ⊢ <;> norm_num at * <;> omega

/-- Cached addition also fits the stricter right-side u32 prescaling limit. -/
theorem wide_right {a : Limbs} (ha : wide a) : RightBound a := by
  intro i
  have h := ha i
  unfold wideCap at h
  unfold rightLimit
  split_ifs at h ⊢ <;> norm_num at * <;> omega

private theorem coefficient_caps (i j : Fin 10) :
    coefficient i j * wideCap i * wideCap j ≤ 19 * 201850880^2 := by
  unfold coefficient wideCap
  split_ifs <;> norm_num <;> omega

theorem wide_term_bound {a b : Limbs} (ha : wide a) (hb : wide b) (i j : Fin 10) :
    term a b i j ≤ 19 * 201850880^2 := by
  exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ (ha i)) (hb j)).trans
    (coefficient_caps i j)

/-- The concrete point caller bounds discharge all 64-bit convolution premises. -/
theorem wide_column_bound {a b : Limbs} (ha : wide a) (hb : wide b) (k : Fin 10) :
    column a b k < 2^63 := by
  have h : column a b k ≤ ∑ _i : Fin 10, 19 * 201850880^2 :=
    Finset.sum_le_sum (fun i _ => wide_term_bound ha hb i (rhsIndex k i))
  norm_num at h ⊢
  omega

/-- The output returns to the tight caller invariant after each multiplication. -/
theorem wide_product_reduced {a b : Limbs} (ha : wide a) (hb : wide b) :
    reduced (product a b) :=
  Reduce64.output_bounds _ (wide_column_bound ha hb)

end Agave.Ed25519.Avx2PointAdd

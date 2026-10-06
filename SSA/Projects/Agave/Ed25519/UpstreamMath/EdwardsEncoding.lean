import SSA.Projects.Agave.Ed25519.UpstreamMath.Canonicality
import Mathlib

/-!
Independent, conditional mathematics of Edwards compression. The hypotheses
are deliberate: this file does not certify primality of the concrete modulus,
nonsquareness of d, or execution of the current decoder. No upstream source
or proof script is incorporated.
-/
namespace Agave.Ed25519.UpstreamMath.Edwards

/-- The affine twisted Edwards relation for a = -1. -/
def OnCurve {K : Type*} [CommRing K] (d x y : K) : Prop :=
  y^2 - x^2 = 1 + d * x^2 * y^2

/-- Equal y-coordinates determine equal x-squares whenever the decoding
denominator is nonzero. This algebraic lemma applies to any field. -/
theorem same_y_same_square {K : Type*} [Field K] (d x₁ x₂ y : K)
    (h₁ : OnCurve d x₁ y) (h₂ : OnCurve d x₂ y)
    (den : 1 + d * y^2 ≠ 0) : x₁^2 = x₂^2 := by
  apply mul_right_cancel₀ den
  unfold OnCurve at h₁ h₂
  linear_combination h₂ - h₁

/-- A square root and its negative have distinct parity modulo an odd prime,
except when they coincide at zero. The prime premise is explicit. -/
theorem square_and_parity_determine_root (modulus : Nat)
    [Fact modulus.Prime] [NeZero modulus] (odd : modulus % 2 = 1)
    (left right : ZMod modulus) (squares : left^2 = right^2)
    (parity : left.val % 2 = right.val % 2) : left = right := by
  cases sq_eq_sq_iff_eq_or_eq_neg.mp squares with
  | inl equal => exact equal
  | inr opposite =>
    by_cases zero : right = 0
    · simpa [zero] using opposite
    · have positive : 0 < right.val := by
        have : right.val ≠ 0 := fun hv => zero ((ZMod.val_eq_zero right).mp hv)
        omega
      have bounded := ZMod.val_lt right
      have complement : left.val = modulus - right.val := by
        calc
          left.val = (-right).val := congrArg ZMod.val opposite
          _ = modulus - right.val := by simp [ZMod.neg_val, zero]
      omega

/-- Canonical compression is injective under explicit denominator and field
hypotheses. The encoded natural is exactly y + parity(x)*2^255. -/
theorem canonical_compression_injective (modulus : Nat)
    [Fact modulus.Prime] [NeZero modulus] (odd : modulus % 2 = 1)
    (bound : modulus ≤ 2^255) (d x₁ y₁ x₂ y₂ : ZMod modulus)
    (curve₁ : OnCurve d x₁ y₁) (curve₂ : OnCurve d x₂ y₂)
    (den : 1 + d * y₁^2 ≠ 0)
    (encoded : Canonicality.encode y₁.val x₁.val =
      Canonicality.encode y₂.val x₂.val) : (x₁, y₁) = (x₂, y₂) := by
  have b₁ := lt_of_lt_of_le (ZMod.val_lt y₁) bound
  have b₂ := lt_of_lt_of_le (ZMod.val_lt y₂) bound
  obtain ⟨ys, signs⟩ := (Canonicality.encode_injective _ _ _ _ b₁ b₂).mp encoded
  have yeq := ZMod.val_injective modulus ys
  subst y₂
  have xs := same_y_same_square d x₁ x₂ y₁ curve₁ curve₂ den
  have xeq := square_and_parity_determine_root modulus odd x₁ x₂ xs signs
  exact Prod.ext xeq rfl

/-- The concrete serial d limbs from solana-ed25519 0.2.4, checked as integers. -/
theorem current_d_limbs :
    (929955233495203 : Nat) + 466365720129213 * 2^51 +
      1662059464998953 * 2^102 + 2033849074728123 * 2^153 +
      1442794654840575 * 2^204 =
      37095705934669439343138083508754565189542113879843219016388785533085940283555 := by decide

/-- The concrete d constant satisfies its defining denominator relation. -/
theorem current_d_relation :
    ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : Nat) *
      121666 + 121665) % Field.p = 0 := by decide

/-- The current serial square-root-of-minus-one constant has the advertised square. -/
theorem current_sqrt_m1_relation :
    (((1718705420411056 : Nat) + 234908883556509 * 2^51 +
      2233514472574048 * 2^102 + 2117202627021982 * 2^153 +
      765476049583133 * 2^204)^2 + 1) % Field.p = 0 := by decide

end Agave.Ed25519.UpstreamMath.Edwards

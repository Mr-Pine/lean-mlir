import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressSqrt
import SSA.Projects.Agave.Ed25519.Proof.Encoding.PointBytes
import Mathlib.FieldTheory.Finite.Basic

/-! Algebraic obligations of the *actual* compressor prefix: one inversion
chain at Z, then two multiplications at X and Y. The RIR prefix must still be
shown to establish the limb representation premises below. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open _root_.Ed25519 Bridge
abbrev K := ZMod p

/-- The imported prefix calls pow22501, pow2k(5), then mul. -/
def invertChain (z : K) : K :=
  (Decompress.pow22501 z).1 ^ (2 ^ 5) * (Decompress.pow22501 z).2

theorem invertChain_exponent (z : K) : invertChain z = z ^ (p - 2) := by
  simp only [invertChain, Decompress.pow22501_eq, ← pow_mul, ← pow_add]
  congr 1

/-- No nonzero assumption is needed: the emitted chain maps zero to zero,
matching the total field inverse. A valid projective representation separately
requires nonzero Z. -/
theorem invertChain_eq_inverse (z : K) : invertChain z = z⁻¹ := by
  rw [invertChain_exponent]
  by_cases hz : z = 0
  · subst z
    simp [p]
  · apply (mul_left_cancel₀ hz)
    rw [mul_inv_cancel₀ hz, ← pow_succ']
    have he : p - 2 + 1 = p - 1 := by norm_num [p]
    rw [he]
    exact ZMod.pow_card_sub_one_eq_one hz

/-- Projective-coordinate premises suffice to identify the two affine products. -/
theorem affine_products (X Y Z : K) (P : CurvePoint)
    (hz : Z ≠ 0) (hx : X = P.x * Z) (hy : Y = P.y * Z) :
    X * invertChain Z = P.x ∧ Y * invertChain Z = P.y := by
  rw [invertChain_eq_inverse, hx, hy]
  simp [mul_assoc, hz]

/-- The lower primitives' value results connect the actual inversion/multiply
schedule to the existing canonical compressor, without a compression premise. -/
theorem serial_projective_compress (X Y Z : K) (P : CurvePoint)
    (x y : Field.Serial) (hz : Z ≠ 0)
    (hx : X = P.x * Z) (hy : Y = P.y * Z)
    (hxm : (Field.serialValue x : K) = X * invertChain Z)
    (hym : (Field.serialValue y : K) = Y * invertChain Z) :
    BitVec.ofNat 1 ((toBytes (fun i => (x i).toNat)).toNat % 2) ++
      BitVec.ofNat 255 (toBytes (fun i => (y i).toNat)).toNat = compress P := by
  obtain ⟨hxa, hya⟩ := affine_products X Y Z P hz hx hy
  exact serial_affine_compress x y P (hxm.trans hxa) (hym.trans hya)

end Agave.Ed25519.Encoding.Compress.Execution

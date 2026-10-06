import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.Algebra
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Arithmetic

/-! Mathematical composition with the exact two-chain reduce64 schedule.
The compiler-program linkage is a separate obligation. -/

namespace Agave.Ed25519.Avx2SquareNegateD
section

theorem decode_eq_decode10 (a : Limbs) : decode a = Field.decode10 a := by
  norm_num [decode, Field.decode10, Field.exponent, Fin.sum_univ_succ, Nat.add_assoc]

/-- The final mathematical coefficient schedule for each of the four elements.
Only element D selects the negative branch. -/
def output (a : Limbs) (negate : Bool) : Limbs :=
  Reduce64.reduce (signedColumns a negate)

theorem reduction_preserves (a : Limbs) (negate : Bool) :
    decode (output a negate) % modulus = decode (signedColumns a negate) % modulus := by
  have h := Reduce64.residue (signedColumns a negate)
  unfold Field.SameField at h
  simpa only [output, decode_eq_decode10, Field.p, modulus] using h.symm

theorem square_result (a : Limbs) :
    decode (output a false) % modulus = decode a ^ 2 % modulus := by
  rw [reduction_preserves]
  exact columns_mod a

theorem negative_square_result {a : Limbs} (ha : Bounded a) :
    (decode (output a true) + decode a ^ 2) % modulus = 0 := by
  rw [Nat.add_mod, reduction_preserves, ← Nat.add_mod]
  exact negated_mod ha

/-- The output reestablishes the limb invariant consumed by the point formulas.
All carry and word bounds come from the original point-coordinate bound. -/
theorem output_bounds {a : Limbs} (ha : Bounded a) (negate : Bool) (i : Fin 10) :
    output a negate i < 2^(if i.val % 2 = 0 then 26 else 25) + 2^18 :=
  Reduce64.output_bounds _ (signedColumns_lt_u63 ha negate) i

theorem output_fits_u32 {a : Limbs} (ha : Bounded a) (negate : Bool) (i : Fin 10) :
    output a negate i < 2^32 := by
  have h := output_bounds ha negate i
  split_ifs at h <;> norm_num at h ⊢ <;> omega

/-- The four inputs prepared by `ExtendedPoint::double`: X,Y,Z,X+Y. -/
def doublingInputs (x y z : Limbs) : Fin 4 → Limbs :=
  ![x, y, z, fun i => x i + y i]

def CoordinateBound (a : Limbs) : Prop :=
  ∀ i, a i < (if i.val % 2 = 0 then 2^26 else 2^25) + 2^18

theorem doubling_inputs_bounded (x y z : Limbs)
    (hx : CoordinateBound x) (hy : CoordinateBound y) (hz : CoordinateBound z)
    (e : Fin 4) : Bounded (doublingInputs x y z e) := by
  fin_cases e
  · exact coordinate_bounded x hx
  · exact coordinate_bounded y hy
  · exact coordinate_bounded z hz
  · exact coordinate_sum_bounded x y hx hy

/-- Exact four mathematical results required by the point-doubling formula. -/
theorem doubling_square_results (x y z : Limbs)
    (hx : CoordinateBound x) (hy : CoordinateBound y) :
    decode (output x false) % modulus = decode x ^ 2 % modulus ∧
    decode (output y false) % modulus = decode y ^ 2 % modulus ∧
    decode (output z false) % modulus = decode z ^ 2 % modulus ∧
    (decode (output (fun i => x i + y i) true) + (decode x + decode y)^2) % modulus = 0 := by
  refine ⟨square_result x, square_result y, square_result z, ?_⟩
  have h := negative_square_result (coordinate_sum_bounded x y hx hy)
  rwa [decode_add] at h

end
end Agave.Ed25519.Avx2SquareNegateD

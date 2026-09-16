import Mathlib.Algebra.BigOperators.Fin

/-!
# Limb representations

A big integer as `n` limbs of `2 ^ baseBits` each, at two levels.

`decodeFn`, `BoundedUpper` and `BoundedLower` are stated over a limb function
`Fin n → R`. The ring is a parameter because the intermediates of a carry
chain are unbounded integers rather than machine limbs.

`Limbs`, `toInts` and `decode` are the vector a machine holds. `toInts` reads
it as a limb function and `decode` is `decodeFn` of that, so the vector level
restates nothing.
-/

namespace LimbRepresentations

/-! ## Limbs by index -/

/-- The value of `n` limbs with radix-`2 ^ baseBits` weights,
`Σ_{i<n} l i · 2^(baseBits·i)`. -/
def decodeFn {R : Type*} [CommSemiring R] (baseBits : ℕ) {n : ℕ} (l : Fin n → R) : R :=
  ∑ i : Fin n, l i * 2 ^ (baseBits * (i : ℕ))

/-- Every limb is at most `u`. -/
def BoundedUpper {n : ℕ} (u : ℤ) (l : Fin n → ℤ) : Prop :=
  ∀ i, l i ≤ u

/-- Every limb is at least `lo`. -/
def BoundedLower {n : ℕ} (lo : ℤ) (l : Fin n → ℤ) : Prop :=
  ∀ i, lo ≤ l i

/-! ## Limbs in a vector -/

/-- `vecLength` limbs of `limbWidth` bits each, as a machine holds them. -/
abbrev Limbs (limbWidth vecLength : Nat) :=
  Vector (BitVec limbWidth) vecLength

/-- The limbs of a vector, read as two's complement integers. -/
def toInts {w n : ℕ} (x : Limbs w n) : Fin n → ℤ := fun i => (x[(i : ℕ)]'i.isLt).toInt

/-- The value a vector of limbs represents. -/
def decode (limbWidth baseBits vecLength : Nat) (limbs : Limbs limbWidth vecLength) : ℤ :=
  decodeFn baseBits (toInts limbs)

end LimbRepresentations

import SSA.Projects.Firedancer.Limbs

namespace R43x6
def limbWidth := 64
def baseBits := 43
def limbCount := 6
def decode := LimbRepresentations.decode limbWidth baseBits limbCount
def decode' := decode ∘ (λ (v: LimbRepresentations.Limbs 64 8) => v.take limbCount)

abbrev BoundedUpper (u: Int) (x: Vector (BitVec 64) 8) : Prop :=
  ∀ (i: Nat) (hi: i < 8), (x[i]'hi).toInt ≤ u
abbrev BoundedLower (l: Int) (x: Vector (BitVec 64) 8) : Prop :=
  ∀ (i: Nat) (hi: i < 8), (x[i]'hi).toInt ≥ l

abbrev UNN (nn: Nat) (x: Vector (BitVec 64) 8) := BoundedUpper (2 ^ nn - 1) x ∧ BoundedLower 0 x
abbrev U44 := UNN 44
abbrev U45 := UNN 45
abbrev U46 := UNN 46
abbrev U47 := UNN 47

abbrev U61 := UNN 61
abbrev U62 := UNN 62

abbrev Unreduced := U47

end R43x6

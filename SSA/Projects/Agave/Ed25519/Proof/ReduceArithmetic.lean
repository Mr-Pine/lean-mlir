import SSA.Projects.Agave.Ed25519.Spec.Field
import Mathlib.Tactic.FinCases

namespace Agave.Ed25519.Field

/-- The exact simultaneous carry ring of `FieldElement2625x4::reduce`.
Carries are taken from the original limbs, not newly reduced ones. -/
def reduceLow (low high : Fin 5 → Nat) : Fin 5 → Nat :=
  ![low 0 % 2^26 + 19*(high 4 / 2^25),
    low 1 % 2^26 + high 0 / 2^25,
    low 2 % 2^26 + high 1 / 2^25,
    low 3 % 2^26 + high 2 / 2^25,
    low 4 % 2^26 + high 3 / 2^25]

def reduceHigh (low high : Fin 5 → Nat) : Fin 5 → Nat :=
  fun i => high i % 2^25 + low i / 2^26

/-- Before taking residues, one reduction subtracts exactly the top carry times p.
No coefficient bound is required for this mathematical identity. -/
theorem reduce_integer (low high : Fin 5 → Nat) :
    decode2625 low high =
      decode2625 (reduceLow low high) (reduceHigh low high) +
        (high 4 / 2^25)*p := by
  have l0 := Nat.mod_add_div (low 0) (2^26)
  have l1 := Nat.mod_add_div (low 1) (2^26)
  have l2 := Nat.mod_add_div (low 2) (2^26)
  have l3 := Nat.mod_add_div (low 3) (2^26)
  have l4 := Nat.mod_add_div (low 4) (2^26)
  have h0 := Nat.mod_add_div (high 0) (2^25)
  have h1 := Nat.mod_add_div (high 1) (2^25)
  have h2 := Nat.mod_add_div (high 2) (2^25)
  have h3 := Nat.mod_add_div (high 3) (2^25)
  have h4 := Nat.mod_add_div (high 4) (2^25)
  norm_num [decode2625, reduceLow, reduceHigh, p, Fin.sum_univ_succ] at *
  omega

theorem reduce_residue (low high : Fin 5 → Nat) :
    decode2625 (reduceLow low high) (reduceHigh low high) % p =
      decode2625 low high % p := by
  rw [reduce_integer low high, Nat.add_mod, Nat.mul_mod]
  simp

/-- Bounds resulting from unrestricted u32 input limbs. -/
theorem reduce_bounds (low high : Fin 5 → Nat)
    (hl : ∀ i, low i < 2^32) (hh : ∀ i, high i < 2^32) :
    Reduced2625 (reduceLow low high) (reduceHigh low high) := by
  have loMod (i : Fin 5) : low i % 2^26 < 2^26 := Nat.mod_lt _ (by decide)
  have hiMod (i : Fin 5) : high i % 2^25 < 2^25 := Nat.mod_lt _ (by decide)
  have loCarry (i : Fin 5) : low i / 2^26 ≤ 63 := by
    have := hl i
    omega
  have hiCarry (i : Fin 5) : high i / 2^25 ≤ 127 := by
    have := hh i
    omega
  constructor
  · intro i
    fin_cases i <;> dsimp [reduceLow]
    all_goals have := loMod 0
    all_goals have := loMod 1
    all_goals have := loMod 2
    all_goals have := loMod 3
    all_goals have := loMod 4
    all_goals have := hiCarry 0
    all_goals have := hiCarry 1
    all_goals have := hiCarry 2
    all_goals have := hiCarry 3
    all_goals have := hiCarry 4
    all_goals norm_num at *
    all_goals omega
  · intro i
    have := hiMod i
    have := loCarry i
    simp only [reduceHigh]
    omega

end Agave.Ed25519.Field

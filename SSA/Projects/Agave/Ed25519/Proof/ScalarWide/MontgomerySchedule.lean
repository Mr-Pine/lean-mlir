import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Montgomery

/-! Reuse the checked five-round natural Montgomery schedule. The nine product
columns here follow the actual Scalar52::montgomery_mul source. The remaining
word bridge must connect the extracted flagged operations to these columns and
this schedule; no machine-correctness premise is disguised as arithmetic. -/

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open Agave.Ed25519.Bridge
open Agave.Ed25519.ScalarReduce32.Arithmetic

/-- Integer represented by five radix-52 limbs. -/
def limbValue (a : Fin 5 → Nat) : Nat :=
  limbs (a 0) (a 1) (a 2) (a 3) (a 4)

/-- The exact nine schoolbook multiplication columns in the pinned routine. -/
def productColumns (a b : Fin 5 → Nat) : Fin 9 → Nat := ![
  a 0 * b 0,
  a 0 * b 1 + a 1 * b 0,
  a 0 * b 2 + a 1 * b 1 + a 2 * b 0,
  a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0,
  a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0,
  a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1,
  a 2 * b 4 + a 3 * b 3 + a 4 * b 2,
  a 3 * b 4 + a 4 * b 3,
  a 4 * b 4]

def columnValue (z : Fin 9 → Nat) : Nat :=
  wideLimbs (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8)

/-- Polynomial identity of the actual multiplication columns. -/
theorem productColumns_value (a b : Fin 5 → Nat) :
    columnValue (productColumns a b) = limbValue a * limbValue b := by
  dsimp [columnValue, productColumns, limbValue, wideLimbs, limbs]
  ring

/-- Adjustment integer and quotient for the shared exact cancellation schedule. -/
def productSchedule (a b : Fin 5 → Nat) : Nat × Nat :=
  let z := productColumns a b
  reduceSchedule (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8)

theorem productSchedule_certificate (a b : Fin 5 → Nat) :
    (productSchedule a b).1 < 2 ^ 260 ∧
      (productSchedule a b).2 * 2 ^ 260 =
        limbValue a * limbValue b + (productSchedule a b).1 * subgroupOrder := by
  have hc := reduceSchedule_certificate
    (productColumns a b 0) (productColumns a b 1) (productColumns a b 2)
    (productColumns a b 3) (productColumns a b 4) (productColumns a b 5)
    (productColumns a b 6) (productColumns a b 7) (productColumns a b 8)
  change (productSchedule a b).1 < 2 ^ 260 ∧
    (productSchedule a b).2 * 2 ^ 260 =
      columnValue (productColumns a b) + (productSchedule a b).1 * subgroupOrder at hc
  rwa [productColumns_value] at hc

/-- Full natural-number Montgomery correctness for either wide-reducer call.
The constant represents `factor` in Montgomery form (one for R, radix for RR). -/
theorem productSchedule_correct (a b : Fin 5 → Nat) (factor : Nat)
    (ha : limbValue a < 2 ^ 260) (hb : limbValue b < subgroupOrder)
    (hconstant : limbValue b % subgroupOrder = (factor * 2 ^ 260) % subgroupOrder) :
    finish (productSchedule a b).2 = (limbValue a * factor) % subgroupOrder ∧
      finish (productSchedule a b).2 < subgroupOrder := by
  have hc := productSchedule_certificate a b
  have hy := ScalarWide.montgomery_quotient_bound
    (limbValue a) (limbValue b) (productSchedule a b).1 (productSchedule a b).2
    ha hb hc.1 hc.2
  have hm := ScalarWide.montgomery_quotient_mod
    (limbValue a) (limbValue b) (productSchedule a b).1 (productSchedule a b).2
    factor hconstant hc.2
  rw [finish_eq_mod _ hy]
  change (productSchedule a b).2 % subgroupOrder = _ ∧
    (productSchedule a b).2 % subgroupOrder < subgroupOrder
  rw [hm]
  exact ⟨rfl, Nat.mod_lt _ (by norm_num [subgroupOrder])⟩

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn1
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn2
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn3
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn4
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn5
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn6
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn7
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryColumn8
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryBounds

/-! The actual wrapping product-column expressions are first interpreted
modulo 2^128; the independently proved limb bounds then remove the modulus. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR

def columnWords (a b : Fin 5 → BitVec 64) (left right : Pointer) : Fin 9 → BitVec 128 :=
  ![(b 0).setWidth 128 * (a 0).setWidth 128,
    column1Word a b left right, column2Word a b left right, column3Word a b left right,
    column4Word a b left right, column5Word a b left right, column6Word a b left right,
    column7Word a b left right, column8Word a b left right]

/-- Exact arbitrary-word interpretation of all nine actual multiplication columns. -/
theorem columnWords_mod (a b : Fin 5 → BitVec 64) (left right : Pointer) (i : Fin 9) :
    (columnWords a b left right i).toNat =
      productColumns (fun j => (a j).toNat) (fun j => (b j).toNat) i % 2 ^ 128 := by
  fin_cases i <;>
    simp only [columnWords, column1Word, column2Word, column3Word, column4Word,
      column5Word, column6Word, column7Word, column8Word, productColumns,
      Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128),
      BitVec.toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]
  all_goals congr 1 <;> ring

/-- Normalized inputs make the complete product accumulation exact in u128. -/
theorem columnWords_toNat (a b : Fin 5 → BitVec 64) (left right : Pointer)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52) (i : Fin 9) :
    (columnWords a b left right i).toNat =
      productColumns (fun j => (a j).toNat) (fun j => (b j).toNat) i := by
  rw [columnWords_mod]
  exact Nat.mod_eq_of_lt ((productColumns_bound _ _ ha hb i).trans (by decide))

/-- Natural carry bounds are available for the values produced by these exact
machine product expressions; no truncation or overflow hypothesis is assumed. -/
theorem columnWords_bound (a b : Fin 5 → BitVec 64) (left right : Pointer)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52) (i : Fin 9) :
    (columnWords a b left right i).toNat < 2 ^ 107 := by
  rw [columnWords_toNat _ _ _ _ ha hb]
  exact productColumns_bound _ _ ha hb i

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

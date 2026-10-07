import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSumRefinement
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperSubtract

/-! The complete mathematical value of the wrapper's addition/subtraction words. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open Agave.Ed25519.Bridge
open Subtraction

/-- The five masked addition words, narrowed without loss. -/
def sum52 (a b : Fin 5 → BitVec 64) : Fin 5 → BitVec 52 :=
  fun i => (sumWords a b i).setWidth 52

theorem sum52_toNat (a b : Fin 5 → BitVec 64) (i : Fin 5) :
    (sum52 a b i).toNat = (sumWords a b i).toNat := by
  rw [sum52, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (sumWords_bound a b i)]

theorem sum52_widen (a b : Fin 5 → BitVec 64) (i : Fin 5) :
    (sum52 a b i).setWidth 64 = sumWords a b i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64), sum52_toNat]

theorem sum52_value (a b : Fin 5 → BitVec 64)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (hsmall : ScalarMontgomeryMul.limbValue (fun i => (a i).toNat) +
      ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) < 2 ^ 260) :
    rawValue (sum52 a b) =
      ScalarMontgomeryMul.limbValue (fun i => (a i).toNat) +
      ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) := by
  simpa only [rawValue, ScalarMontgomeryMul.limbValue, sum52_toNat] using
    sumWords_value a b ha hb hsmall

/-- Two canonical Montgomery outputs add to less than twice L; one exact
borrow/addback pass therefore returns the canonical modular sum. -/
theorem wrapper_modular_sum (a b : Fin 5 → BitVec 64)
    (ha : ∀ i, (a i).toNat < 2 ^ 52) (hb : ∀ i, (b i).toNat < 2 ^ 52)
    (hac : ScalarMontgomeryMul.limbValue (fun i => (a i).toNat) < subgroupOrder)
    (hbc : ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) < subgroupOrder) :
    ScalarMontgomeryMul.limbValue (fun i => (ScalarMontgomeryMul.tailWords (sum52 a b) i).toNat) =
      (ScalarMontgomeryMul.limbValue (fun i => (a i).toNat) +
        ScalarMontgomeryMul.limbValue (fun i => (b i).toNat)) % subgroupOrder := by
  have h2 : ScalarMontgomeryMul.limbValue (fun i => (a i).toNat) +
      ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) < 2 * subgroupOrder := by omega
  have hbound : 2 * subgroupOrder < 2 ^ 260 := by decide
  have hv := sum52_value a b ha hb (h2.trans hbound)
  change Agave.Ed25519.ScalarReduce32.Arithmetic.limbs _ _ _ _ _ = _
  rw [ScalarMontgomeryMul.tailWords_value, hv]
  exact Agave.Ed25519.ScalarReduce32.Arithmetic.finish_eq_mod _ h2

end Agave.Ed25519.Verifier.Execution.ScalarWide

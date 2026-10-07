import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.InputWords
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ProductRefinement

/-! Arithmetic refinement of the actual reducer product and carry words. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Arithmetic
open Agave.Ed25519.Bridge
open Agave.Ed25519.Verifier.Execution
open ScalarMontgomeryMul
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 512

/-- The literal source R operand, as radix-52 limbs. -/
def reductionR : Fin 5 → BitVec 64 :=
  ![4302102966953709#64, 1049714374468698#64, 4503599278581019#64,
    4503599627370495#64, 17592186044415#64]

theorem reductionR_bound (i : Fin 5) : (reductionR i).toNat < 2 ^ 52 := by
  fin_cases i <;> decide +kernel

theorem reductionR_value : limbValue (fun i => (reductionR i).toNat) = sourceR := rfl

theorem reductionR_canonical : limbValue (fun i => (reductionR i).toNat) < subgroupOrder := by
  exact sourceR_lt_ell

/-- The nine columns are the word expressions used by the multiplication slice. -/
def reductionProducts (x : Fin 5 → BitVec 64) : Fin 9 → BitVec 128 :=
  ![productWord0 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord1 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord2 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord3 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord4 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord5 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord6 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord7 (x 0) (x 1) (x 2) (x 3) (x 4),
    productWord8 (x 0) (x 1) (x 2) (x 3) (x 4)]

theorem reductionProducts_eq (x : Fin 5 → BitVec 64) (left right : Pointer) :
    reductionProducts x = columnWords x reductionR left right := by
  funext i
  fin_cases i <;>
    simp only [reductionProducts, reductionR, columnWords,
      productWord0, productWord1, productWord2, productWord3, productWord4, productWord5, productWord6, productWord7, productWord8,
      column1Word, column2Word, column3Word, column4Word, column5Word, column6Word, column7Word, column8Word,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  all_goals norm_num <;> ring

theorem reductionProducts_bound (x : Fin 5 → BitVec 64)
    (hx : ∀ i, (x i).toNat < 2 ^ 52) (i : Fin 9) :
    (reductionProducts x i).toNat < 2 ^ 107 := by
  rw [reductionProducts_eq x default default]
  exact columnWords_bound x reductionR default default hx reductionR_bound i

end Agave.Ed25519.ScalarReduce32.Execution

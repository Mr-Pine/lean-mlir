import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductRefinement
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MontgomeryPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryWordCorrect

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Arithmetic
open Agave.Ed25519.Bridge
open Agave.Ed25519.Verifier.Execution
open ScalarMontgomeryMul
open ScalarWide.Subtraction
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 512

/-- The normalized five carry words, with a proved lossless top truncation. -/
def reductionQuotient (x : Fin 5 → BitVec 64) : Fin 5 → BitVec 52 :=
  fun i => (wordQuotientLimbs (reductionProducts x) i).setWidth 52

theorem reductionQuotient_widen (x : Fin 5 → BitVec 64)
    (hx : ∀ i, (x i).toNat < 2 ^ 52) (i : Fin 5) :
    (reductionQuotient x i).setWidth 64 = wordQuotientLimbs (reductionProducts x) i := by
  simp only [reductionQuotient, reductionProducts_eq x default default]
  exact quotient52_widen x reductionR default default hx reductionR_bound reductionR_canonical i



end Agave.Ed25519.ScalarReduce32.Execution

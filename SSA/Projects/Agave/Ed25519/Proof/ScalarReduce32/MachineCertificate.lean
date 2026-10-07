import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MontgomeryRefinement

/-! The machine quotient discharges the carry premises of `finish_correct`.
The quotient is the five actual carry words, after a proved lossless truncation;
no execution or arithmetic certificate is assumed from the caller. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Arithmetic
open Agave.Ed25519.Verifier.Execution
open ScalarMontgomeryMul
open ScalarWide.Subtraction

/-- Adjustment integer obtained from the exact five cancellation rounds. -/
def reductionAdjustment (bits : BitVec 256) : Nat :=
  (productSchedule (fun i => (inputWords bits i).toNat)
    (fun i => (reductionR i).toNat)).1

/-- Exact carry identity for the actual reducer's normalized quotient words. -/
theorem reduction_carry_certificate (bits : BitVec 256) :
    reductionAdjustment bits < montgomeryModulus ∧
      rawValue (reductionQuotient (inputWords bits)) * montgomeryModulus =
        bits.toNat * sourceR + reductionAdjustment bits * UpstreamMath.Canonicality.ell := by
  have hq := quotient52_value (inputWords bits) reductionR default default
    (inputWords_bound bits) reductionR_bound reductionR_canonical
  have hc := productSchedule_certificate (fun i => (inputWords bits i).toNat)
    (fun i => (reductionR i).toNat)
  have hi : limbValue (fun i => (inputWords bits i).toNat) = bits.toNat :=
    inputWords_value bits
  rw [hi, reductionR_value] at hc
  have he : reductionQuotient (inputWords bits) =
      quotient52 (inputWords bits) reductionR default default := by
    funext i
    change (wordQuotientLimbs (reductionProducts (inputWords bits)) i).setWidth 52 = _
    rw [reductionProducts_eq (inputWords bits) default default]
    rfl
  rw [he, hq]
  exact hc

/-- The general arithmetic certificate now applies with all machine premises
proved for every input, including inputs with the high bit set. -/
theorem reduction_finish_correct (bits : BitVec 256) :
    finish (rawValue (reductionQuotient (inputWords bits))) =
      bits.toNat % UpstreamMath.Canonicality.ell ∧
    finish (rawValue (reductionQuotient (inputWords bits))) <
      UpstreamMath.Canonicality.ell := by
  have hc := reduction_carry_certificate bits
  exact finish_correct bits.toNat (reductionAdjustment bits) _ bits.isLt hc.1 hc.2

end Agave.Ed25519.ScalarReduce32.Execution

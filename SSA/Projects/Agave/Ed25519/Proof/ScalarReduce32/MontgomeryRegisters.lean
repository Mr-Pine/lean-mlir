import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MontgomeryPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WordSchedule

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The five actual source registers contain the shared carry schedule. -/
theorem montgomeryPhaseEnv_quotient (E : Env program.Γ) (z : Fin 9 → BitVec 128) :
    (montgomeryPhaseEnv E z).read (%286) = .value (wordQuotientLimbs z 0) ∧
    (montgomeryPhaseEnv E z).read (%294) = .value (wordQuotientLimbs z 1) ∧
    (montgomeryPhaseEnv E z).read (%300) = .value (wordQuotientLimbs z 2) ∧
    (montgomeryPhaseEnv E z).read (%306) = .value (wordQuotientLimbs z 3) ∧
    (montgomeryPhaseEnv E z).read (%308) = .value (wordQuotientLimbs z 4) := by
  let t0 := z 0
  let d0 := cancellationDigit t0
  let c0 := cancellationCarry t0
  let t1 := carryGapSum0 d0 (z 1) c0
  let d1 := cancellationDigit t1
  let c1 := cancellationCarry t1
  let t2 := carryGapSum1 d0 d1 (z 2) c1
  let d2 := cancellationDigit t2
  let c2 := cancellationCarry t2
  let t3 := carryGapSum2 d1 d2 (z 3) c2
  let d3 := cancellationDigit t3
  let c3 := cancellationCarry t3
  let t4 := carryGapSum3 d0 d2 d3 (z 4) c3
  let d4 := cancellationDigit t4
  let c4 := cancellationCarry t4
  let t5 := carryGapSum4 d1 d3 d4 (z 5) c4
  let t6 := carryGapSum5 d2 d4 (z 6) (t5 >>> 52)
  let t7 := carryGapSum6 d3 (z 7) (t6 >>> 52)
  let t8 := carryGapSum7 d4 (z 8) (t7 >>> 52)
  have h5 : t5 = wordUpperSums z 0 := by
    change z 5 + ((d1.setWidth 128) <<< 44) + d3.setWidth 128 * 1367801#128 +
      d4.setWidth 128 * 3916664325105025#128 + c4 =
      ((d1.setWidth 128) <<< 44) + z 5 + d3.setWidth 128 * 1367801#128 +
      d4.setWidth 128 * 3916664325105025#128 + c4
    rw [BitVec.add_comm (z 5) ((d1.setWidth 128) <<< 44)]
  have h6 : t6 = wordUpperSums z 1 := by
    change ((d2.setWidth 128) <<< 44) + z 6 + d4.setWidth 128 * 1367801#128 +
      (t5 >>> 52) = _
    rw [h5]
    rfl
  have h7 : t7 = wordUpperSums z 2 := by
    change ((d3.setWidth 128) <<< 44) + z 7 + (t6 >>> 52) = _
    rw [h6]
    rfl
  have h8 : t8 = wordUpperSums z 3 := by
    change ((d4.setWidth 128) <<< 44) + z 8 + (t7 >>> 52) = _
    rw [h7]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change LeanMLIR.RIR.PoisonOr.value (t5.setWidth 64 &&& 4503599627370495#64) = _
    rw [h5]
    rfl
  · change LeanMLIR.RIR.PoisonOr.value (t6.setWidth 64 &&& 4503599627370495#64) = _
    rw [h6]
    rfl
  · change LeanMLIR.RIR.PoisonOr.value (t7.setWidth 64 &&& 4503599627370495#64) = _
    rw [h7]
    rfl
  · change LeanMLIR.RIR.PoisonOr.value (t8.setWidth 64 &&& 4503599627370495#64) = _
    rw [h8]
    rfl
  · change LeanMLIR.RIR.PoisonOr.value ((t8 >>> 52).setWidth 64) = _
    rw [h8]
    rfl

end Agave.Ed25519.ScalarReduce32.Execution

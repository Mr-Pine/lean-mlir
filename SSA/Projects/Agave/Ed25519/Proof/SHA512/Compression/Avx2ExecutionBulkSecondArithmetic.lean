import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionArithmetic

/-! Bounded byte-counter arithmetic for the imported second-block bb15 loop. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem bulkSecond_index_add (r : Nat) (hhi : r < 80) :
    Operation.add {nsw := true, nuw := true}
      (.value (BitVec.ofNat 64 (8 * r))) (.value 8#64) =
      .value (BitVec.ofNat 64 (8 * (r + 1))) := by
  interval_cases r <;> decide

theorem bulkSecond_index_gep (r : Nat) (hhi : r < 80) :
    Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 (8 * r))) =
      .value (Int.ofNat (8 * r)) := by
  interval_cases r <;> decide

theorem bulkSecond_index_eq640 (r : Nat) (hhi : r < 80) :
    (BitVec.ofNat 64 (8 * (r + 1)) == 640#64) = decide (r + 1 = 80) := by
  interval_cases r <;> decide

end Agave.Ed25519.SHA512.Execution.Avx2

import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.FieldCall
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialContracts

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts

/-- The CFG contracts' field reads and the flat word trace decode the same
physical X,Y,Z,T record, without a pointer-layout premise. -/
theorem readPoint_words (s : GlobalState) (p : Pointer) :
    readPoint s p = unsignedPoint (pointFromWords (readPointWords s p)) := by
  apply PointArithmetic.Extended.ext <;> funext i <;> fin_cases i <;>
    simp [readPoint, readField, unsignedPoint, pointFromWords, readPointWords,
      unsigned, readLimbs, Pointer.add_add]

theorem readCached_words (s : GlobalState) (p : Pointer) :
    readCached s p = unsignedPoint (cacheFromWords (readPointWords s p)) := by
  apply PointArithmetic.Extended.ext <;> funext i <;> fin_cases i <;>
    simp [readCached, readField, unsignedPoint, cacheFromWords, pointFromWords,
      readPointWords, unsigned, readLimbs, Pointer.add_add]

theorem pointPost_writesOnly (s : GlobalState) (p : Pointer) (v : PointWords)
    (blocks : Nat) (hwf : s.WF) (hp : SmallRange s.mem p 160) :
    WritesOnly p 160 s (pointPost s p v blocks) := by
  refine ⟨pointPost_wf s hwf p v blocks, ?_, ?_, ?_⟩
  · exact Nat.le_add_right _ _
  · intro id
    exact storePointWords_allocationShape s.mem p v id
  · intro q bits hd
    exact readAt_storePointWords_frame s.mem p q v bits hp hd

end Agave.Ed25519.SerialPoint.Execution

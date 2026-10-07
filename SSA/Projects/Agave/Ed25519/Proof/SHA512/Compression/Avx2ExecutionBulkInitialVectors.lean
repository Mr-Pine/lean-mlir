import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialVectorsBytes
import LeanMLIR.Dialects.LLVM.Basic

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Both loaded native pairs become the exact independent big-endian words. -/
theorem bulkInitialWords_native (first second : Bytes) (i j : Nat) :
    bulkInitialWords (readWordNative first i) (readWordNative first (i+1))
      (readWordNative second j) (readWordNative second (j+1)) =
    bulkVec (readWordBE first i) (readWordBE first (i+1))
      (readWordBE second j) (readWordBE second (j+1)) := by
  have hs := bulkInitialShuffle_native first second i j
  unfold bulkInitialWords
  rw [hs, bulkInitial_bitcast_wrap]
  ext k hk
  interval_cases k <;>
    simp [Ty.unflatten, Ty.extractVecElem, bulkVec, Ty.wrap_vec]
  · change (BitVec.packLanes _).extractLsb' (8*0) (8*8) = _
    rw [BitVec.extractLsb'_packLanes_run _ 8 0 (by decide)]
    simp [BitVec.packLanes, readWordBE_concat, Vector.tail_ofFn,
      -Vector.tail_eq_cast_extract]
    rw [BitVec.zero_width_append]
    rfl
  · change (BitVec.packLanes _).extractLsb' (8*8) (8*8) = _
    rw [BitVec.extractLsb'_packLanes_run _ 8 8 (by decide)]
    simp [BitVec.packLanes, readWordBE_concat, Vector.tail_ofFn,
      -Vector.tail_eq_cast_extract]
    rw [BitVec.zero_width_append]
    rfl
  · change (BitVec.packLanes _).extractLsb' (8*16) (8*8) = _
    rw [BitVec.extractLsb'_packLanes_run _ 8 16 (by decide)]
    simp [BitVec.packLanes, readWordBE_concat, Vector.tail_ofFn,
      -Vector.tail_eq_cast_extract]
    rw [BitVec.zero_width_append]
    rfl
  · change (BitVec.packLanes _).extractLsb' (8*24) (8*8) = _
    rw [BitVec.extractLsb'_packLanes_run _ 8 24 (by decide)]
    simp [BitVec.packLanes, readWordBE_concat, Vector.tail_ofFn,
      -Vector.tail_eq_cast_extract]
    rw [BitVec.zero_width_append]
    rfl

end Agave.Ed25519.SHA512.Execution.Avx2

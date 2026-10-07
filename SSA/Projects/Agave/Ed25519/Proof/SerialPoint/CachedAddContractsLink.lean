import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointContractMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedAddExecution

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
open DoubleBase.SerialContracts

/-- Discharge the serial CFG's cached-add helper contract using the exact
imported body, its four actual field multiplications, and concrete readback. -/
theorem cached_add_contract :
    BinaryPointContract cached_add.call 160 readCached cachedAddCompleted := by
  intro s out input cached hwf hout hin hcache _ _ hP hC
  have hp : PointTight (unsignedPoint (pointFromWords (readPointWords s input))) := by
    rwa [readPoint_words] at hP
  have hc : PointBounded (unsignedPoint (cacheFromWords (readPointWords s cached))) := by
    rwa [readCached_words] at hC
  let output := cachedAddWordTrace (readPointWords s input) (readPointWords s cached)
  let final := pointPost s out output 6
  have hread : readPoint final out = cachedAddCompleted (readPoint s input) (readCached s cached) := by
    rw [readPoint_words, pointPost_readback s out output 6 hout,
      readPoint_words, readCached_words]
    exact cachedAddWordTrace_unsigned _ _ hp hc
  refine ⟨final, cached_add_call out input cached s hwf hout hin hcache,
    pointPost_writesOnly s out output 6 hwf hout, hread, ?_⟩
  rw [hread]
  exact cachedAddCompleted_bounded _ _ hP hC

end Agave.Ed25519.SerialPoint.Execution

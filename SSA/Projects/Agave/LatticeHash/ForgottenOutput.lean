/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Equivalence
import SSA.Projects.Agave.LatticeHash.ExecutableCompression
import SSA.Projects.Agave.LatticeHash.Forgotten

/-!
Concrete final-output witnesses for the forgotten-guard trace. Only the first
u16 of each 2048-byte LtHash is needed to prove that the returned values differ.
The vector implementation is used solely to make kernel reduction efficient;
its equality with scalarCompress is itself proved in ExecutableCompression.lean.
No collision-freedom, cryptographic assumption, native evaluation, or
long-message fallback correctness is used.
-/
namespace AgaveForgotten
open Blake3Compression.Executable

-- Kernel reduction of the concrete BLAKE3 blocks needs deeper recursion.
set_option maxRecDepth 4096 in
theorem concrete_zc_first (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    AgaveConcrete.hash longHash [90, 67] 0 = 27344#16 := by
  rw [AgaveConcrete.hash_short longHash _ (by simp)]
  unfold AgaveConcrete.oneChunk AgaveConcrete.oneChunkWords AgaveBatchControl.scalarXofAt AgaveConcrete.xof
  rw [← vectorCompress_eq]
  rfl

set_option maxRecDepth 4096 in
theorem concrete_ic_first (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    AgaveConcrete.hash longHash [73, 67] 0 = 5968#16 := by
  rw [AgaveConcrete.hash_short longHash _ (by simp)]
  unfold AgaveConcrete.oneChunk AgaveConcrete.oneChunkWords AgaveBatchControl.scalarXofAt AgaveConcrete.xof
  rw [← vectorCompress_eq]
  rfl

set_option maxRecDepth 4096 in
theorem concrete_ac_first (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    AgaveConcrete.hash longHash [65, 67] 0 = 47808#16 := by
  rw [AgaveConcrete.hash_short longHash _ (by simp)]
  unfold AgaveConcrete.oneChunk AgaveConcrete.oneChunkWords AgaveBatchControl.scalarXofAt AgaveConcrete.xof
  rw [← vectorCompress_eq]
  rfl

/-- Both LtHashes returned by the two `take` calls in `forgottenTrace`, after
    applying the concrete BLAKE3 model to every recorded hash input. -/
def returnedLtHashes (longHash : AgaveConcrete.Message → AgaveConcrete.Value)
    (width : Nat) : AgaveConcrete.Value × AgaveConcrete.Value :=
  let messages := forgottenTrace width
  (AgaveStaging.scalar (AgaveConcrete.hash longHash) messages.1,
   AgaveStaging.scalar (AgaveConcrete.hash longHash) messages.2)

theorem first_returns_agree (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    (returnedLtHashes longHash 1).1 = (returnedLtHashes longHash 8).1 ∧
    (returnedLtHashes longHash 8).1 = (returnedLtHashes longHash 16).1 := by
  simp only [returnedLtHashes, width1_counterexample, width8_counterexample,
    width16_counterexample, and_self]

theorem width1_return_first (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    (returnedLtHashes longHash 1).2 0 = 27344#16 := by
  simpa only [returnedLtHashes, width1_counterexample, AgaveStaging.scalar_singleton]
    using concrete_zc_first longHash

theorem width8_return_first (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    (returnedLtHashes longHash 8).2 0 = 5968#16 := by
  simpa only [returnedLtHashes, width8_counterexample, AgaveStaging.scalar_singleton]
    using concrete_ic_first longHash

theorem width16_return_first (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    (returnedLtHashes longHash 16).2 0 = 47808#16 := by
  simpa only [returnedLtHashes, width16_counterexample, AgaveStaging.scalar_singleton]
    using concrete_ac_first longHash

/-- All three returned LtHashes actually differ. This is stronger than unequal
    inputs and needs no assumed injectivity of BLAKE3. -/
theorem final_outputs_pairwise_different
    (longHash : AgaveConcrete.Message → AgaveConcrete.Value) :
    (returnedLtHashes longHash 1).2 ≠ (returnedLtHashes longHash 8).2 ∧
    (returnedLtHashes longHash 8).2 ≠ (returnedLtHashes longHash 16).2 ∧
    (returnedLtHashes longHash 1).2 ≠ (returnedLtHashes longHash 16).2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h := congrArg (fun v => (v 0).toNat) h
    rw [width1_return_first, width8_return_first] at h
    change 27344 = 5968 at h
    omega
  · intro h
    have h := congrArg (fun v => (v 0).toNat) h
    rw [width8_return_first, width16_return_first] at h
    change 5968 = 47808 at h
    omega
  · intro h
    have h := congrArg (fun v => (v 0).toNat) h
    rw [width1_return_first, width16_return_first] at h
    change 27344 = 47808 at h
    omega

end AgaveForgotten

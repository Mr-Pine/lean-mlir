/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchPrefixTargets16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchHeaderSemantics16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootScalar16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression
open BatchRefinement16
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable def rootInputAt16 (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) : BatchRootCopy16.Input5.Valuation :=
  BatchRootRun16.input5 (ambient16 entry src len out sched panic ms)
    (BatchTranspose16.rootTarget16
      (transposeAt16 (ambient16 entry src len out sched panic ms) ms iteration)).args

/-- The actual root-copy block uses exactly the two entry scratch allocations. -/
theorem rootCopyEnv16 (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :
    rootInputAt16 entry src len out sched panic ms iteration ⟨44, rfl⟩ =
      PoisonOr.value (BatchEntry16.scratch entry 0) ∧
    rootInputAt16 entry src len out sched panic ms iteration ⟨43, rfl⟩ =
      PoisonOr.value (BatchEntry16.scratch entry 1) ∧
    rootInputAt16 entry src len out sched panic ms iteration ⟨143, rfl⟩ =
      PoisonOr.value 1024#64 := by
  constructor
  · rfl
  constructor <;> rfl

/-- The copied-root successor carries the scalar-prefix chaining values and
the exact decoded block length and flags from the actual header. -/
theorem rootNextAt16 (entry : GlobalState) (src len out sched panic : Pointer)
    (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat)
    (hms : ∀ lane, (ms lane).length ≤ 1024) :
    BatchRootCopy16.next5 (rootInputAt16 entry src len out sched panic ms iteration) =
      BatchXofLoop16.rootTarget (rootCVAt16 ms iteration)
        (rootSizes16 ms iteration) (rootFlags16 ms iteration) 0 := by
  apply root_target
  · rfl
  · exact BatchHeader16.size_words16 entry src len out sched panic ms iteration hms
  · exact BatchHeader16.flags_words16 entry src len out sched panic ms iteration hms

end AgaveLatticeHash.MLIR

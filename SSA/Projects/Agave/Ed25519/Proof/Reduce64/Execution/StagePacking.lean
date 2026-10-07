import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageTypes
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Execute the 23 bitcast, poison-mask, and shuffle instructions. The word
arithmetic enters solely through `ReducedRegisters`, so this proof normalizes
packing without expanding the carry expressions. -/
theorem packing_cont {α : Type} (E : Env program.Γ) (s : GlobalState)
    (dst src : Pointer) (z : Columns4)
    (κ : Env program.Γ × GlobalState → PoisonOr α) (result : PoisonOr α)
    (hargs : E.args = (program.args (.value dst) (.value src)).get)
    (hconstants : KernelConstants E)
    (hregisters : ReducedRegisters E z)
    (hnext : ∀ E', E'.args = (program.args (.value dst) (.value src)).get →
      KernelConstants E' → PackedRegisters E' z →
      (program.entry.runBodyFrom E' 129 s >>= κ) = result) :
    (program.entry.runBodyFrom E 106 s >>= κ) = result := by
  rcases hconstants with ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC33, hC51⟩
  rcases hregisters with ⟨hV68, hV73, hV78, hV82, hV84, hV88, hV90, hV94, hV100, hV103⟩
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  step_pure [bitcast_wrap, laneWord, halfMask]
  try subst S
  apply hnext E
  · assumption
  · unfold KernelConstants
    env_reads
  · unfold PackedRegisters
    reduce_env_reads
    all_goals
      apply Vector.ext
      intro i hi
      interval_cases i <;>
        simp [packedOutput, reduceLanes, packPair, Word.reduce, low32, BitVec.extractLsb'_and, Ty.wrap_vec]

end Agave.Ed25519.Reduce64.Execution

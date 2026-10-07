import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Avx2SquareNegateD.Execution
open LeanMLIR.RIR
open Reduce64.Execution

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 10000

/-- The only registers written by the nine-instruction store tail. -/
def storesEnv (E : Env program.Γ) (r : Pointer) : Env program.Γ :=
  E[%356 := .value (r.add 32#64), %357 := .value (r.add 64#64), %358 := .value (r.add 96#64), %359 := .value (r.add 128#64)]

set_option maxHeartbeats 1200000 in
/-- Execute the actual final five stores with their arithmetic inputs abstract.
This proof is independent of the convolution, carry, and bitcast computations. -/
theorem stores_run (E : Env program.Γ) (s : GlobalState) (r : Pointer) (v : Blocks)
    (hr : SmallRange s.mem r 160)
    (harg : E.read (%arg0) = .value r)
    (h0 : E.read (%336) = Ty.wrap (v 0))
    (h1 : E.read (%341) = Ty.wrap (v 1))
    (h2 : E.read (%345) = Ty.wrap (v 2))
    (h3 : E.read (%350) = Ty.wrap (v 3))
    (h4 : E.read (%355) = Ty.wrap (v 4)) :
    program.entry.runBodyFrom E 356 s =
      .value (storesEnv E r, {s with mem := storeBlocks s.mem r v}) := by
  -- Preserve the entry argument map when the stepping tactics seal each new environment.
  have hArgs : E.args = E.args := rfl
  simp only [Env.read] at harg
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  step_store [harg, h0]
  have hgep := hr.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, harg, GepIndex.inboundsOffset,
    Operation.gepInboundsIndex, Operation.GepSignedRange]
  clear hgep
  step_store [h1]
  have hgep := hr.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, harg, GepIndex.inboundsOffset,
    Operation.gepInboundsIndex, Operation.GepSignedRange]
  clear hgep
  step_store [h2]
  have hgep := hr.gep (k := 96) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, harg, GepIndex.inboundsOffset,
    Operation.gepInboundsIndex, Operation.GepSignedRange]
  clear hgep
  step_store [h3]
  have hgep := hr.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, harg, GepIndex.inboundsOffset,
    Operation.gepInboundsIndex, Operation.GepSignedRange]
  clear hgep
  step_store [h4]
  rw [BasicBlock.runBodyFrom_done (by decide +kernel)]
  simp only [EffectM.pure_eq]
  rw [hS]
  subst_vars
  simp [storesEnv, storeBlocks]

end Agave.Ed25519.Avx2SquareNegateD.Execution

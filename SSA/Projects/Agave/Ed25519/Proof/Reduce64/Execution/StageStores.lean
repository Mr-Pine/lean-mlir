import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageTypes
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The store tail changes only its four address registers. -/
def storesEnv (E : Env program.Γ) (dst : Pointer) : Env program.Γ :=
  E[%127 := .value (dst.add 32#64), %128 := .value (dst.add 64#64),
    %129 := .value (dst.add 96#64), %130 := .value (dst.add 128#64)]

/-- The final nine actual instructions, with all packed arithmetic inputs
abstract. No source-memory premise or arithmetic bound enters this proof. -/
theorem stores_run (E : Env program.Γ) (s : GlobalState) (dst src : Pointer)
    (z : Columns4) (hdst : SmallRange s.mem dst 160)
    (hargs : E.args = (program.args (.value dst) (.value src)).get)
    (hconstants : KernelConstants E) (hregisters : PackedRegisters E z) :
    program.entry.runBodyFrom E 129 s =
      .value (storesEnv E dst, {s with mem := storeOutputs s.mem dst z}) := by
  rcases hconstants with ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC33, hC51⟩
  rcases hregisters with ⟨hV107, hV112, hV116, hV121, hV126⟩
  have hf0 := hdst.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hdst.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hdst.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hdst.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hdst.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  step_store [hV107]
  have hgep := hdst.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_store [hV112]
  have hgep := hdst.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_store [hV116]
  have hgep := hdst.gep (k := 96) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_store [hV121]
  have hgep := hdst.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_store [hV126]
  rw [BasicBlock.runBodyFrom_done (by decide +kernel)]
  simp only [EffectM.pure_eq]
  rw [hS]
  subst_vars
  simp only [storesEnv, storeOutputs]
  rfl

end Agave.Ed25519.Reduce64.Execution

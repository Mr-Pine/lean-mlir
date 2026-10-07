import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageTypes
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact instruction slice [54, 67); its continuation receives only
live register facts, keeping the remainder of the kernel outside this proof. -/
theorem carryA_cont {α : Type} (E : Env program.Γ) (s : GlobalState)
    (dst src : Pointer) (z : Columns4)
    (κ : Env program.Γ × GlobalState → PoisonOr α) (result : PoisonOr α)
    (hsrc : SmallRange s.mem src 320)
    (hreads : ∀ k : Fin 10,
      (Ty.vec 4 64).unflatten
        (s.mem.readAt (src.add (BitVec.ofNat 64 (32 * k.val))) 256) = Ty.wrap (z k))
    (hargs : E.args = (program.args (.value dst) (.value src)).get)
    (hconstants : KernelConstants E)
    (hnext : ∀ E', E'.args = (program.args (.value dst) (.value src)).get →
      KernelConstants E' → CarryA E' z →
      (program.entry.runBodyFrom E' 67 s >>= κ) = result) :
    (program.entry.runBodyFrom E 54 s >>= κ) = result := by
  rcases hconstants with ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC33, hC51⟩
  have hf0 := hsrc.fits_add (k := 0) (count := 32) (by decide)
  have hz0 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt src 256)) = Ty.wrap (t := .vec 4 64) (z 0) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 0
  have hf1 := hsrc.fits_add (k := 32) (count := 32) (by decide)
  have hz1 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 32#64) 256)) = Ty.wrap (t := .vec 4 64) (z 1) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 1
  have hf4 := hsrc.fits_add (k := 128) (count := 32) (by decide)
  have hz4 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 128#64) 256)) = Ty.wrap (t := .vec 4 64) (z 4) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 4
  have hf5 := hsrc.fits_add (k := 160) (count := 32) (by decide)
  have hz5 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 160#64) 256)) = Ty.wrap (t := .vec 4 64) (z 5) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 5
  simp only [Pointer.add_zero] at hf0
  have hgep := hsrc.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz0] inline
  step_load [hz1] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  have hgep := hsrc.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  have hgep := hsrc.gep (k := 160) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz4] inline
  step_load [hz5] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  try subst S
  apply hnext E
  · assumption
  · unfold KernelConstants
    env_reads
  · unfold CarryA
    reduce_env_reads

end Agave.Ed25519.Reduce64.Execution

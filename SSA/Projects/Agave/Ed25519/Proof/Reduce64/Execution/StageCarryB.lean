import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageTypes
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact instruction slice [67, 85); its continuation receives only
live register facts, keeping the remainder of the kernel outside this proof. -/
theorem carryB_cont {α : Type} (E : Env program.Γ) (s : GlobalState)
    (dst src : Pointer) (z : Columns4)
    (κ : Env program.Γ × GlobalState → PoisonOr α) (result : PoisonOr α)
    (hsrc : SmallRange s.mem src 320)
    (hreads : ∀ k : Fin 10,
      (Ty.vec 4 64).unflatten
        (s.mem.readAt (src.add (BitVec.ofNat 64 (32 * k.val))) 256) = Ty.wrap (z k))
    (hargs : E.args = (program.args (.value dst) (.value src)).get)
    (hconstants : KernelConstants E)
    (hregisters : CarryA E z)
    (hnext : ∀ E', E'.args = (program.args (.value dst) (.value src)).get →
      KernelConstants E' → CarryB E' z →
      (program.entry.runBodyFrom E' 85 s >>= κ) = result) :
    (program.entry.runBodyFrom E 67 s >>= κ) = result := by
  rcases hconstants with ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC33, hC51⟩
  rcases hregisters with ⟨hV56, hV57, hV63, hV64⟩
  have hf2 := hsrc.fits_add (k := 64) (count := 32) (by decide)
  have hz2 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 64#64) 256)) = Ty.wrap (t := .vec 4 64) (z 2) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 2
  have hf6 := hsrc.fits_add (k := 192) (count := 32) (by decide)
  have hz6 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 192#64) 256)) = Ty.wrap (t := .vec 4 64) (z 6) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 6
  have hf3 := hsrc.fits_add (k := 96) (count := 32) (by decide)
  have hz3 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 96#64) 256)) = Ty.wrap (t := .vec 4 64) (z 3) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 3
  have hf7 := hsrc.fits_add (k := 224) (count := 32) (by decide)
  have hz7 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 224#64) 256)) = Ty.wrap (t := .vec 4 64) (z 7) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 7
  have hgep := hsrc.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz2] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  have hgep := hsrc.gep (k := 192) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz6] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  have hgep := hsrc.gep (k := 96) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz3] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  have hgep := hsrc.gep (k := 224) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz7] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  try subst S
  apply hnext E
  · assumption
  · unfold KernelConstants
    env_reads
  · unfold CarryB
    reduce_env_reads

end Agave.Ed25519.Reduce64.Execution

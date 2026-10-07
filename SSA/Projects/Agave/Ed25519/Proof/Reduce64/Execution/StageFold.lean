import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.StageTypes
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

attribute [local implicit_reducible] Ty.width
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


private theorem emitted_t4 (w : Word.Columns) :
    (Word.t3 w >>> 25) + (w 4 &&& 67108863#64) = Word.t4 w := by
  exact BitVec.add_comm _ _

private theorem emitted_t8 (w : Word.Columns) :
    (Word.t7 w >>> 25) + w 8 = Word.t8 w := by
  exact BitVec.add_comm _ _

private theorem emitted_u5 (w : Word.Columns) :
    (Word.t4 w >>> 26) + (Word.t5 w &&& 33554431#64) = Word.u5 w := by
  exact BitVec.add_comm _ _

private theorem emitted_t9 (w : Word.Columns) :
    (Word.t8 w >>> 26) + w 9 = Word.t9 w := by
  exact BitVec.add_comm _ _

private theorem emitted_u0 (w : Word.Columns) :
    ((Word.t9 w >>> 25) &&& 67108863#64) * 19#64 +
      (w 0 &&& 67108863#64) = Word.u0 w := by
  exact BitVec.add_comm _ _

private theorem emitted_u1 (w : Word.Columns) :
    ((Word.t9 w >>> 51) * 19#64 + (Word.t1 w &&& 33554431#64)) +
      (Word.u0 w >>> 26) = Word.u1 w := by
  unfold Word.u1 Word.carry
  rw [← BitVec.shiftRight_add]
  rw [BitVec.add_comm ((Word.t9 w >>> 51) * 19#64)]

/-- Exact instruction slice [85, 106); its continuation receives only
live register facts, keeping the remainder of the kernel outside this proof. -/
theorem fold_cont {α : Type} (E : Env program.Γ) (s : GlobalState)
    (dst src : Pointer) (z : Columns4)
    (κ : Env program.Γ × GlobalState → PoisonOr α) (result : PoisonOr α)
    (hsrc : SmallRange s.mem src 320)
    (hreads : ∀ k : Fin 10,
      (Ty.vec 4 64).unflatten
        (s.mem.readAt (src.add (BitVec.ofNat 64 (32 * k.val))) 256) = Ty.wrap (z k))
    (hargs : E.args = (program.args (.value dst) (.value src)).get)
    (hconstants : KernelConstants E)
    (hregisters : CarryB E z)
    (hnext : ∀ E', E'.args = (program.args (.value dst) (.value src)).get →
      KernelConstants E' → ReducedRegisters E' z →
      (program.entry.runBodyFrom E' 106 s >>= κ) = result) :
    (program.entry.runBodyFrom E 85 s >>= κ) = result := by
  rcases hconstants with ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC33, hC51⟩
  rcases hregisters with ⟨hV57, hV64, hV68, hV69, hV73, hV74, hV78, hV82⟩
  have hf8 := hsrc.fits_add (k := 256) (count := 32) (by decide)
  have hz8 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 256#64) 256)) = Ty.wrap (t := .vec 4 64) (z 8) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 8
  have hf9 := hsrc.fits_add (k := 288) (count := 32) (by decide)
  have hz9 : Ty.wrap (t := .vec 4 64) (Vector.ofFn fun i => Ty.extractVecElem 4 64 i
    (s.mem.readAt (src.add 288#64) 256)) = Ty.wrap (t := .vec 4 64) (z 9) := by
    simpa [Ty.unflatten_vec, BitVec.ofNat_eq_ofNat] using hreads 9
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  have hgep := hsrc.gep (k := 256) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz8] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  have hgep := hsrc.gep (k := 288) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange]
  clear hgep
  step_load [hz9] inline
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  step_pure [laneWord, carry_mask26_flags, carry_mask25_flags, low_mul19_flags, high_mul19_flags, low_fold_flags, high_fold_flags, final_carry_flags]
  try subst S
  apply hnext E
  · assumption
  · unfold KernelConstants
    env_reads
  · unfold ReducedRegisters
    reduce_env_reads
    all_goals
      apply Vector.ext
      intro i hi
      interval_cases i <;>
        simp [laneWord, Ty.wrap_vec, emitted_t4, emitted_t8, emitted_u5, emitted_t9, emitted_u0, emitted_u1]

end Agave.Ed25519.Reduce64.Execution

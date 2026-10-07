import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2kProgram
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareWord
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Execution
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ExecutionMemory

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
open Encoding.Decompress.Execution.Pow2k (program)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 10000 in
/-- Execute the unchanged three-block `pow2k` body at exponent one, including
the loop's terminating branch and all five stores. Inputs may alias output;
the word-level execution needs no arithmetic bound. -/
theorem square_call (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40) :
    program.call (program.args (.value r) (.value a) (.value 1#32)) s =
      .value (.nil, { s with mem := storeLimbs s.mem r (squareMachine (readLimbs s a)) }) := by
  have hr0 := hr.fits_add (k := 0) (count := 8) (by decide)
  have hr8 := hr.fits_add (k := 8) (count := 8) (by decide)
  have hr16 := hr.fits_add (k := 16) (count := 8) (by decide)
  have hr24 := hr.fits_add (k := 24) (count := 8) (by decide)
  have hr32 := hr.fits_add (k := 32) (count := 8) (by decide)
  have ha0 := ha.fits_add (k := 0) (count := 8) (by decide)
  have ha8 := ha.fits_add (k := 8) (count := 8) (by decide)
  have ha16 := ha.fits_add (k := 16) (count := 8) (by decide)
  have ha24 := ha.fits_add (k := 24) (count := 8) (by decide)
  have ha32 := ha.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hr0 ha0
  func_init
  block_init
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_load
  have hgep := ha.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  have hgep := ha.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  have hgep := ha.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  have hgep := ha.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  finish_block
  block_init
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  finish_block
  block_init
  step_store
  have hgep := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  finish_block
  rw [hS]
  erase_frame
  subst_vars
  simp [storeLimbs, squareMachine, squareWordColumns, wordSchedule,
    readLimbs, Pointer.add]

/-- Exact one-iteration execution of the imported square helper, with its
natural limb result and the bound needed by the next point operation. -/
theorem square_call_correct (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hA : Bounded (unsigned (readLimbs s a))) :
    ∃ output : Fin 5 → BitVec 64,
      program.call (program.args (.value r) (.value a) (.value 1#32)) s =
        .value (.nil, { s with mem := storeLimbs s.mem r output }) ∧
      unsigned output = sq (unsigned (readLimbs s a)) ∧
      Tight (unsigned output) ∧
      value (unsigned output) = value (unsigned (readLimbs s a)) ^ 2 := by
  exact ⟨squareMachine (readLimbs s a), square_call r a s hwf hr ha,
    squareMachine_unsigned _ hA, squareMachine_tight _ hA,
    squareMachine_value _ hA⟩

theorem square_call_readback (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hA : Bounded (unsigned (readLimbs s a))) :
    ∃ final : GlobalState,
      program.call (program.args (.value r) (.value a) (.value 1#32)) s =
        .value (.nil, final) ∧
      unsigned (readLimbs final r) = sq (unsigned (readLimbs s a)) ∧
      Tight (unsigned (readLimbs final r)) ∧
      value (unsigned (readLimbs final r)) = value (unsigned (readLimbs s a)) ^ 2 := by
  obtain ⟨output, hcall, hout, htight, hvalue⟩ :=
    square_call_correct r a s hwf hr ha hA
  refine ⟨{ s with mem := storeLimbs s.mem r output }, hcall, ?_⟩
  rw [readLimbs_storeLimbs s r output hr]
  exact ⟨hout, htight, hvalue⟩

end Agave.Ed25519.SerialPoint.Execution

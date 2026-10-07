import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytesProgram
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ToBytesMemory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.ToBytesExecution
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Execution

namespace Agave.Ed25519.Encoding.Decompress.Execution.ToBytes
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Encoding.RIR

attribute [-simp] BitVec.shiftLeft_add_distrib in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The input is fully loaded before any output store, so overlapping buffers are allowed. -/
theorem program_run (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 32) (ha : SmallRange s.mem a 40) :
    program.run (program.args (.value r) (.value a)) s =
      .value (.nil, { s with mem := storeBytes s.mem r (machine (SerialFieldMul.readLimbs s a)) }) := by
  have hr0 := hr.fits_add (k := 0) (count := 1) (by decide)
  have hr1 := hr.fits_add (k := 1) (count := 1) (by decide)
  have hr2 := hr.fits_add (k := 2) (count := 1) (by decide)
  have hr3 := hr.fits_add (k := 3) (count := 1) (by decide)
  have hr4 := hr.fits_add (k := 4) (count := 1) (by decide)
  have hr5 := hr.fits_add (k := 5) (count := 1) (by decide)
  have hr6 := hr.fits_add (k := 6) (count := 1) (by decide)
  have hr7 := hr.fits_add (k := 7) (count := 1) (by decide)
  have hr8 := hr.fits_add (k := 8) (count := 1) (by decide)
  have hr9 := hr.fits_add (k := 9) (count := 1) (by decide)
  have hr10 := hr.fits_add (k := 10) (count := 1) (by decide)
  have hr11 := hr.fits_add (k := 11) (count := 1) (by decide)
  have hr12 := hr.fits_add (k := 12) (count := 1) (by decide)
  have hr13 := hr.fits_add (k := 13) (count := 1) (by decide)
  have hr14 := hr.fits_add (k := 14) (count := 1) (by decide)
  have hr15 := hr.fits_add (k := 15) (count := 1) (by decide)
  have hr16 := hr.fits_add (k := 16) (count := 1) (by decide)
  have hr17 := hr.fits_add (k := 17) (count := 1) (by decide)
  have hr18 := hr.fits_add (k := 18) (count := 1) (by decide)
  have hr19 := hr.fits_add (k := 19) (count := 1) (by decide)
  have hr20 := hr.fits_add (k := 20) (count := 1) (by decide)
  have hr21 := hr.fits_add (k := 21) (count := 1) (by decide)
  have hr22 := hr.fits_add (k := 22) (count := 1) (by decide)
  have hr23 := hr.fits_add (k := 23) (count := 1) (by decide)
  have hr24 := hr.fits_add (k := 24) (count := 1) (by decide)
  have hr25 := hr.fits_add (k := 25) (count := 1) (by decide)
  have hr26 := hr.fits_add (k := 26) (count := 1) (by decide)
  have hr27 := hr.fits_add (k := 27) (count := 1) (by decide)
  have hr28 := hr.fits_add (k := 28) (count := 1) (by decide)
  have hr29 := hr.fits_add (k := 29) (count := 1) (by decide)
  have hr30 := hr.fits_add (k := 30) (count := 1) (by decide)
  have hr31 := hr.fits_add (k := 31) (count := 1) (by decide)
  have ha0 := ha.fits_add (k := 0) (count := 8) (by decide)
  have ha8 := ha.fits_add (k := 8) (count := 8) (by decide)
  have ha16 := ha.fits_add (k := 16) (count := 8) (by decide)
  have ha24 := ha.fits_add (k := 24) (count := 8) (by decide)
  have ha32 := ha.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hr0 ha0
  have hs := toBytesSafe3 (SerialFieldMul.readLimbs s a 0) (SerialFieldMul.readLimbs s a 1) (SerialFieldMul.readLimbs s a 2) (SerialFieldMul.readLimbs s a 3) (SerialFieldMul.readLimbs s a 4)
  dsimp only [SerialFieldMul.readLimbs] at hs
  norm_num at hs
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41⟩
  rw [Func.run_runFrom_eq]
  extract_state
  extract_env
  block_init
  simp only [hS] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_load inline
  have hgep := ha.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  have hgep := ha.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  have hgep := ha.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  have hgep := ha.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure [h0, h1]
  step_pure [h2, h3]
  step_pure [h4, h5]
  step_pure [h6, h7]
  step_pure [h8, h9]
  step_pure [h10, h11]
  step_pure [h12, h13]
  step_pure
  step_pure [h14, h15]
  step_pure
  step_pure [h16, h17]
  step_pure
  step_pure [h18, h19]
  step_pure
  step_pure [h20, h21]
  step_pure
  step_pure [h22, h23]
  step_pure [h24, h25]
  step_pure
  step_pure [h26, h27]
  step_pure
  step_pure [h28, h29]
  step_pure
  step_pure
  step_pure [h30, h31]
  step_pure
  step_pure
  step_pure [h32, h33]
  step_pure
  step_pure
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure
  step_pure [masked_shift_3_signed, masked_shift_3_unsigned]
  step_pure [boundary_disjoint_3]
  have hgep := hr.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure [masked_shift_6_signed, masked_shift_6_unsigned]
  step_pure [boundary_disjoint_6]
  have hgep := hr.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure [masked_shift_1_signed, masked_shift_1_unsigned]
  step_pure [boundary_disjoint_1]
  have hgep := hr.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure [masked_shift_4_signed, masked_shift_4_unsigned]
  step_pure [boundary_disjoint_4]
  have hgep := hr.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure [last_byte_trunc_signed, last_byte_trunc_unsigned]
  step_store
  finish_block
  rw [hS]
  try erase_frame
  subst_vars
  simp [machine, carryMachine, reverseCarry, quotientCarry, weakWord, rawBytes, storeBytes, SerialFieldMul.readLimbs, Pointer.add]

/-- The standalone call reclaims no allocations; its output is the same exact
store state as `program_run`. Kept at the original API for existing callers. -/
theorem program_call (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 32) (ha : SmallRange s.mem a 40) :
    program.call (program.args (.value r) (.value a)) s =
      .value (.nil, { s with mem := storeBytes s.mem r (machine (SerialFieldMul.readLimbs s a)) }) := by
  exact Func.call_eq_of_run_eq (program_run r a s hwf hr ha)
    (wf_storeBytes hwf r _) rfl

set_option maxRecDepth 10000 in
/-- Exact helper execution and full canonical output readback, without a limb
bound assumption. Every limb is an arbitrary input u64. -/
theorem program_correct (r a : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 32) (ha : SmallRange s.mem a 40) :
    ∃ t, program.call (program.args (.value r) (.value a)) s = .value (.nil, t) ∧
      t.alloc = s.alloc ∧
      (t.mem.readAt r 256).toNat = Field.serialValue (SerialFieldMul.readLimbs s a) % modulus := by
  refine ⟨_, program_call r a s hwf hr ha, rfl, ?_⟩
  exact storeBytes_canonical_value s.mem r (SerialFieldMul.readLimbs s a) hr

end Agave.Ed25519.Encoding.Decompress.Execution.ToBytes

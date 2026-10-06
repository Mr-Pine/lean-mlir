import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Lift
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Word
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Machine
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.SerialFieldMul
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
section

def readLimbs (s : GlobalState) (p : Pointer) : Fin 5 → BitVec 64 :=
  fun i => s.mem.readAt (p.add (BitVec.ofNat 64 (8*i.val))) 64

def storeLimbs (m : MemoryState) (p : Pointer) (v : Fin 5 → BitVec 64) : MemoryState :=
  ((((m.storeAt p (v 0)).storeAt (p.add 8) (v 1)).storeAt (p.add 16) (v 2)).storeAt
    (p.add 24) (v 3)).storeAt (p.add 32) (v 4)

set_option maxHeartbeats 1200000 in
/-- Exact RIR execution, including all five stores. Inputs may alias the output:
all input loads precede the first output store. -/
theorem kernel_call (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40) (hb : SmallRange s.mem b 40) :
    kernel.call (kernel.args (.value r) (.value a) (.value b)) s =
      .value (.nil, { s with mem := storeLimbs s.mem r (machine (readLimbs s a) (readLimbs s b)) }) := by
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
  have hb0 := hb.fits_add (k := 0) (count := 8) (by decide)
  have hb8 := hb.fits_add (k := 8) (count := 8) (by decide)
  have hb16 := hb.fits_add (k := 16) (count := 8) (by decide)
  have hb24 := hb.fits_add (k := 24) (count := 8) (by decide)
  have hb32 := hb.fits_add (k := 32) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hr0 ha0 hb0
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
  have hgep := hb.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  have hgep := hb.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  have hgep := hb.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  have hgep := hb.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_load
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  have hgep := ha.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  have hgep := ha.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  have hgep := ha.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  have hgep := ha.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
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
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
  step_pure [wide_mul_nooverflow, final_add_nooverflow]
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
  simp [storeLimbs, machine, readLimbs, Pointer.add]

end
end Agave.Ed25519.SerialFieldMul

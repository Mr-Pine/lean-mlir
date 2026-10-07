import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleSquareCall
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleTrace
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.VectorMemory

namespace Agave.Ed25519.SerialPoint.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)
open Encoding.Decompress.Execution.Pow2k (program)

attribute [local irreducible] machine squareMachine

attribute [-simp] readLimbs_explicit in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- Exact full point-double call; the four call cut points use the actual
imported square body, not a postulated field-operation contract. -/
theorem double_call (r p : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (hp : SmallRange s.mem p 120) :
    (double program.call).call (double.args (.value r) (.value p)) s =
      .value (.nil, { alloc := ⟨s.alloc.nextFreeBlock + 5⟩,
                      mem := storePointWords s.mem r (doubleWordTrace (readPointWords s p)) }) := by
  have hrfits := hr.fits
  have hr0 := hr.fits_add (k := 0) (count := 8) (by decide)
  have hr8 := hr.fits_add (k := 8) (count := 8) (by decide)
  have hr16 := hr.fits_add (k := 16) (count := 8) (by decide)
  have hr24 := hr.fits_add (k := 24) (count := 8) (by decide)
  have hr32 := hr.fits_add (k := 32) (count := 8) (by decide)
  have hr40 := hr.fits_add (k := 40) (count := 8) (by decide)
  have hr48 := hr.fits_add (k := 48) (count := 8) (by decide)
  have hr56 := hr.fits_add (k := 56) (count := 8) (by decide)
  have hr64 := hr.fits_add (k := 64) (count := 8) (by decide)
  have hr72 := hr.fits_add (k := 72) (count := 8) (by decide)
  have hr80 := hr.fits_add (k := 80) (count := 8) (by decide)
  have hr88 := hr.fits_add (k := 88) (count := 8) (by decide)
  have hr96 := hr.fits_add (k := 96) (count := 8) (by decide)
  have hr104 := hr.fits_add (k := 104) (count := 8) (by decide)
  have hr112 := hr.fits_add (k := 112) (count := 8) (by decide)
  have hr120 := hr.fits_add (k := 120) (count := 8) (by decide)
  have hr128 := hr.fits_add (k := 128) (count := 8) (by decide)
  have hr136 := hr.fits_add (k := 136) (count := 8) (by decide)
  have hr144 := hr.fits_add (k := 144) (count := 8) (by decide)
  have hr152 := hr.fits_add (k := 152) (count := 8) (by decide)
  have hrfield0 := smallRange_add hr (k := 0) (count := 40) (by decide)
  have hrfield40 := smallRange_add hr (k := 40) (count := 40) (by decide)
  have hrfield80 := smallRange_add hr (k := 80) (count := 40) (by decide)
  have hrfield120 := smallRange_add hr (k := 120) (count := 40) (by decide)
  have hpfits := hp.fits
  have hp0 := hp.fits_add (k := 0) (count := 8) (by decide)
  have hp8 := hp.fits_add (k := 8) (count := 8) (by decide)
  have hp16 := hp.fits_add (k := 16) (count := 8) (by decide)
  have hp24 := hp.fits_add (k := 24) (count := 8) (by decide)
  have hp32 := hp.fits_add (k := 32) (count := 8) (by decide)
  have hp40 := hp.fits_add (k := 40) (count := 8) (by decide)
  have hp48 := hp.fits_add (k := 48) (count := 8) (by decide)
  have hp56 := hp.fits_add (k := 56) (count := 8) (by decide)
  have hp64 := hp.fits_add (k := 64) (count := 8) (by decide)
  have hp72 := hp.fits_add (k := 72) (count := 8) (by decide)
  have hp80 := hp.fits_add (k := 80) (count := 8) (by decide)
  have hp88 := hp.fits_add (k := 88) (count := 8) (by decide)
  have hp96 := hp.fits_add (k := 96) (count := 8) (by decide)
  have hp104 := hp.fits_add (k := 104) (count := 8) (by decide)
  have hp112 := hp.fits_add (k := 112) (count := 8) (by decide)
  have hpfield0 := smallRange_add hp (k := 0) (count := 40) (by decide)
  have hpfield40 := smallRange_add hp (k := 40) (count := 40) (by decide)
  have hpfield80 := smallRange_add hp (k := 80) (count := 40) (by decide)
  have hpvector0 := hp.fits_add (k := 0) (count := 16) (by decide)
  have hpv0 := smallRange_add hp (k := 0) (count := 16) (by decide)
  have hpvector16 := hp.fits_add (k := 16) (count := 16) (by decide)
  have hpv16 := smallRange_add hp (k := 16) (count := 16) (by decide)
  have hpvector40 := hp.fits_add (k := 40) (count := 16) (by decide)
  have hpv40 := smallRange_add hp (k := 40) (count := 16) (by decide)
  have hpvector56 := hp.fits_add (k := 56) (count := 16) (by decide)
  have hpv56 := smallRange_add hp (k := 56) (count := 16) (by decide)
  simp only [Pointer.add_zero] at hr0 hp0 hrfield0 hpfield0 hpvector0 hpv0
  func_init
  have hpv0_initial : SmallRange S₀.mem p 16 := by
    simpa only [hS] using hpv0
  have hpv16_initial : SmallRange S₀.mem (p.add 16#64) 16 := by
    simpa only [hS] using hpv16
  have hpv40_initial : SmallRange S₀.mem (p.add 40#64) 16 := by
    simpa only [hS] using hpv40
  have hpv56_initial : SmallRange S₀.mem (p.add 56#64) 16 := by
    simpa only [hS] using hpv56
  block_init
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
  step_alloca with slot26
  have hs26 : SmallRange S.mem slot26 40 := by
    rw [hS, hslot26]
    exact smallRange_alloca_self _ _ (by decide)
  have hs26_scalar := hs26.fits_add (k := 0) (count := 8) (by decide)
  have hs26_vector := hs26.fits_add (k := 0) (count := 16) (by decide)
  simp only [Pointer.add_zero] at hs26_scalar hs26_vector
  step_alloca with slot27
  have hs27 : SmallRange S.mem slot27 40 := by
    rw [hS, hslot27]
    exact smallRange_alloca_self _ _ (by decide)
  have hs27_scalar := hs27.fits_add (k := 0) (count := 8) (by decide)
  have hs27_vector := hs27.fits_add (k := 0) (count := 16) (by decide)
  simp only [Pointer.add_zero] at hs27_scalar hs27_vector
  step_alloca with slot28
  have hs28 : SmallRange S.mem slot28 40 := by
    rw [hS, hslot28]
    exact smallRange_alloca_self _ _ (by decide)
  have hs28_scalar := hs28.fits_add (k := 0) (count := 8) (by decide)
  have hs28_vector := hs28.fits_add (k := 0) (count := 16) (by decide)
  simp only [Pointer.add_zero] at hs28_scalar hs28_vector
  step_alloca with slot29
  have hs29 : SmallRange S.mem slot29 40 := by
    rw [hS, hslot29]
    exact smallRange_alloca_self _ _ (by decide)
  have hs29_scalar := hs29.fits_add (k := 0) (count := 8) (by decide)
  have hs29_vector := hs29.fits_add (k := 0) (count := 16) (by decide)
  simp only [Pointer.add_zero] at hs29_scalar hs29_vector
  step_alloca with slot30
  have hs30 : SmallRange S.mem slot30 40 := by
    rw [hS, hslot30]
    exact smallRange_alloca_self _ _ (by decide)
  have hs30_scalar := hs30.fits_add (k := 0) (count := 8) (by decide)
  have hs30_vector := hs30.fits_add (k := 0) (count := 16) (by decide)
  simp only [Pointer.add_zero] at hs30_scalar hs30_vector
  step_pure
  -- Field-call cut point 0: exact imported pow2k(1).
  step_call using double_square_call
  step_pure
  have hgep := hp.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  -- Field-call cut point 1: exact imported pow2k(1).
  step_call using double_square_call
  step_pure
  have hgep := hp.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  -- Field-call cut point 2: exact imported pow2k(1).
  step_call using double_square_call
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs28.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs28.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs28.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs28.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure
  step_pure
  step_pure
  step_pure
  have hgep := hp.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hp.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  have hgep := hp.gep (k := 56) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hp.gep (k := 72) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_load [load_two_words]
  step_load [load_two_words]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_store
  have hgep := hs27.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load [load_two_words]
  step_load [load_two_words]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_store
  have hgep := hs27.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  step_pure
  -- Field-call cut point 3: exact imported pow2k(1).
  step_call using double_square_call
  step_pure
  step_pure
  step_load
  have hgep := hs29.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  have hgep := hs29.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  have hgep := hs29.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  have hgep := hs29.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs30.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs30.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs30.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs30.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs26.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs26.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs26.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hs26.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_store
  have hgep := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 48) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 56) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 72) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 88) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 96) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 104) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 112) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 120) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 136) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 144) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  have hgep := hr.gep (k := 152) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_store
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  finish_block

  rw [hS]
  subst_vars
  simp only [storeLimbs, Fits.storeAt_iff] at hslot26_fits hs26_scalar hs26_vector hslot27_fits hs27_scalar hs27_vector hslot28_fits hs28_scalar hs28_vector hslot29_fits hs29_scalar hs29_vector hslot30_fits hs30_scalar hs30_vector
  simp only [readLimbs_explicit]
  simp (disch := first | assumption | rfl | ne_fact | fits_fact | disjoint_fact | decide | omega)
    only [readAt_storeLimbs_ne, readAt_alloca_ne, Pointer.add_id]
  simp only [storeLimbs]
  erase_frame
  simp (disch := first | assumption | rfl | ne_fact | fits_fact | disjoint_fact | decide | omega)
    [mlir_mem, MemoryState.readAt_storeAt_disjoint, MemoryState.readAt_storeAt_self,
      MemoryState.readAt_storeAt_add,
      readAt_alloca_ne, storePointWords, doubleWordTrace, readPointWords, Pointer.add_add, offsetInBits_alloca, offsetInBits_alloca_add,
      storeLimbs, readLimbs_explicit, readLimbs, Nat.add_assoc, load_two_words,
      packed_two_low, packed_two_high]

/-- Output observation of the exact double body, with full caller framing. -/
theorem double_readback (r p : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 160) (hp : SmallRange s.mem p 120)
    (hP : ProjectiveTight (unsignedPoint (pointFromWords (readPointWords s p)))) :
    ∃ final : GlobalState,
      (double program.call).call (double.args (.value r) (.value p)) s =
        .value (.nil, final) ∧
      unsignedPoint (pointFromWords (readPointWords final r)) =
        doubleCompleted (unsignedPoint (pointFromWords (readPointWords s p))) ∧
      (∀ q bits, (Range.of q bits).Disjoint (Range.of r 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  let output := doubleWordTrace (readPointWords s p)
  let final : GlobalState :=
    { alloc := ⟨s.alloc.nextFreeBlock + 5⟩, mem := storePointWords s.mem r output }
  have hread : readPointWords final r = output := by
    funext k
    exact storePointWords_readAt s.mem r output hr k
  refine ⟨final, double_call r p s hwf hr hp, ?_, ?_⟩
  · rw [hread]
    exact doubleWordTrace_projective_unsigned _ hP
  · intro q bits hd
    exact readAt_storePointWords_frame s.mem r q output bits hr hd

end Agave.Ed25519.SerialPoint.Execution

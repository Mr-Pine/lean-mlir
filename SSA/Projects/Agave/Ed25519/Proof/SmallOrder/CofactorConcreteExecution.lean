import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorLoopExecution
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorState
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.Linked
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleTrace
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorCall
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorValidPoint

/-! Exact k=3 execution of the pinned cofactor body. The three projective
double calls are reduced to one local call contract; all ten field
multiplications use their proved RIR body. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint SerialPoint.Execution SerialFieldMul
open Reduce64.Execution (SmallRange)
open Verifier.Execution.PointMulByPow2
set_option maxRecDepth 24000
set_option maxHeartbeats 8000000

@[local mlir_transport] theorem pointPost_fits (h : Fits s.mem q bits)
    (p : Pointer) (v : PointWords) (blocks : Nat) :
    Fits (pointPost s p v blocks).mem q bits := by
  unfold pointPost storePointWords
  exact h.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt.storeAt

@[local mlir_transport] theorem pointPost_range (h : SmallRange s.mem q bytes)
    (p : Pointer) (v : PointWords) (blocks : Nat) :
    SmallRange (pointPost s p v blocks).mem q bytes := smallRange_storePointWords h _ _

@[local mlir_read] theorem pointWords_frame_ne (m : MemoryState) (out q : Pointer)
    (v : PointWords) (bits : Nat) (hne : out.id ≠ q.id) :
    (storePointWords m out v).readAt q bits = m.readAt q bits := by
  unfold storePointWords
  simp (disch := exact Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne))
    only [MemoryState.readAt_storeAt_disjoint]

attribute [local irreducible] storePointWords doubleWordTrace

attribute [local mlir_transport] pointPost_wf

attribute [-simp] readLimbs_explicit in
/-- All outer instruction, branch, and phase obligations are discharged for
exactly k=3. The lower doubling call is isolated for the linked specialization. -/
theorem cofactor_call_three_of_double
    (doubleCall : Vals [.ptr, .ptr] → EffectM (Vals []))
    (hdouble : ∀ (out input : Pointer) (s : GlobalState), s.WF →
      SmallRange s.mem out 160 → SmallRange s.mem input 120 →
      doubleCall
        (.cons (.value out) (.cons (.value input) .nil)) s =
        .value (.nil, pointPost s out (doubleWordTrace (readPointWords s input)) 5))
    (out input : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    (program ⟨doubleCall, kernel.call⟩).call (.cons (.value out) (.cons (.value input) (.cons (.value 3#32) .nil))) s =
      .value (.nil, cofactorState s out input) := by
  have hout0 := smallRange_add hout (k := 0) (count := 40) (by decide)
  have houtf0 := hout.fits_add (k := 0) (count := 40) (by decide)
  have hout40 := smallRange_add hout (k := 40) (count := 40) (by decide)
  have houtf40 := hout.fits_add (k := 40) (count := 40) (by decide)
  have hout80 := smallRange_add hout (k := 80) (count := 40) (by decide)
  have houtf80 := hout.fits_add (k := 80) (count := 40) (by decide)
  have hout120 := smallRange_add hout (k := 120) (count := 40) (by decide)
  have houtf120 := hout.fits_add (k := 120) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hout0 houtf0
  have hin0 := smallRange_add hin (k := 0) (count := 40) (by decide)
  have hinf0 := hin.fits_add (k := 0) (count := 40) (by decide)
  have hin40 := smallRange_add hin (k := 40) (count := 40) (by decide)
  have hinf40 := hin.fits_add (k := 40) (count := 40) (by decide)
  have hin80 := smallRange_add hin (k := 80) (count := 40) (by decide)
  have hinf80 := hin.fits_add (k := 80) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hin0 hinf0
  func_init
  block_init
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_alloca with slot6
  have hslot6 : SmallRange S.mem slot6 160 := by
    rw [hS, hslot6]
    exact smallRange_alloca_self _ _ (by decide)
  have hslot6_0 := smallRange_add hslot6 (k := 0) (count := 40) (by decide)
  have hslot6f_0 := hslot6.fits_add (k := 0) (count := 40) (by decide)
  have hslot6_40 := smallRange_add hslot6 (k := 40) (count := 40) (by decide)
  have hslot6f_40 := hslot6.fits_add (k := 40) (count := 40) (by decide)
  have hslot6_80 := smallRange_add hslot6 (k := 80) (count := 40) (by decide)
  have hslot6f_80 := hslot6.fits_add (k := 80) (count := 40) (by decide)
  have hslot6_120 := smallRange_add hslot6 (k := 120) (count := 40) (by decide)
  have hslot6f_120 := hslot6.fits_add (k := 120) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hslot6_0 hslot6f_0
  step_alloca with slot7
  have hslot7 : SmallRange S.mem slot7 120 := by
    rw [hS, hslot7]
    exact smallRange_alloca_self _ _ (by decide)
  have hslot7_0 := smallRange_add hslot7 (k := 0) (count := 40) (by decide)
  have hslot7f_0 := hslot7.fits_add (k := 0) (count := 40) (by decide)
  have hslot7_40 := smallRange_add hslot7 (k := 40) (count := 40) (by decide)
  have hslot7f_40 := hslot7.fits_add (k := 40) (count := 40) (by decide)
  have hslot7_80 := smallRange_add hslot7 (k := 80) (count := 40) (by decide)
  have hslot7f_80 := hslot7.fits_add (k := 80) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hslot7_0 hslot7f_0
  step_alloca with slot8
  have hslot8 : SmallRange S.mem slot8 120 := by
    rw [hS, hslot8]
    exact smallRange_alloca_self _ _ (by decide)
  have hslot8_0 := smallRange_add hslot8 (k := 0) (count := 40) (by decide)
  have hslot8f_0 := hslot8.fits_add (k := 0) (count := 40) (by decide)
  have hslot8_40 := smallRange_add hslot8 (k := 40) (count := 40) (by decide)
  have hslot8f_40 := hslot8.fits_add (k := 40) (count := 40) (by decide)
  have hslot8_80 := smallRange_add hslot8 (k := 80) (count := 40) (by decide)
  have hslot8f_80 := hslot8.fits_add (k := 80) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hslot8_0 hslot8f_0
  step_alloca with slot9
  have hslot9 : SmallRange S.mem slot9 160 := by
    rw [hS, hslot9]
    exact smallRange_alloca_self _ _ (by decide)
  have hslot9_0 := smallRange_add hslot9 (k := 0) (count := 40) (by decide)
  have hslot9f_0 := hslot9.fits_add (k := 0) (count := 40) (by decide)
  have hslot9_40 := smallRange_add hslot9 (k := 40) (count := 40) (by decide)
  have hslot9f_40 := hslot9.fits_add (k := 40) (count := 40) (by decide)
  have hslot9_80 := smallRange_add hslot9 (k := 80) (count := 40) (by decide)
  have hslot9f_80 := hslot9.fits_add (k := 80) (count := 40) (by decide)
  have hslot9_120 := smallRange_add hslot9 (k := 120) (count := 40) (by decide)
  have hslot9f_120 := hslot9.fits_add (k := 120) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hslot9_0 hslot9f_0
  step_pure
  step_pure
  have hgep := hin.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hslot8.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_memcpy
  have hgep := hin.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hslot8.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_memcpy
  step_memcpy
  step_pure
  step_pure
  finish_block
  all_goals try (simp at hbr)
  block_init
  have hgep := hslot9.gep (k := 120) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hslot9.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hslot9.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hslot7.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hslot7.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  finish_block
  all_goals try (simp at hbr)
  have hel : LoopRegisters E slot9 slot8 slot7 := by
    constructor <;> simp (disch := decide) [mlir_env, *]
  have hef : FinalRegisters E out slot6 slot8 := by
    constructor
    · change E.args 0 = .value out
      rw [hArgs]
      rfl
    · simp (disch := decide) [mlir_env, *]
    · simp (disch := decide) [mlir_env, *]
  have hcounter : E.read (%27) = .value 0#32 := by simp (disch := decide) [mlir_env, *]
  have hlimit : E.read (%14) = .value 2#32 := by simp (disch := decide) [mlir_env, *]
  have hrun := two_loops_run ⟨doubleCall, kernel.call⟩ rfl hdouble E S out slot6 slot9 slot8 slot7
    hel hef hcounter hlimit hwf hout hslot6 hslot9 hslot8 hslot7 (by ne_fact)
  rw [hrun]
  simp only [EffectM.bind_eq, PoisonOr.value_bind]
  rw [hS]
  subst_vars
  simp (disch := first | assumption | ne_fact | fits_fact | disjoint_fact | omega)
    only [cofactorState, initialState, copyState, MemoryState.readAt_storeAt_disjoint,
      Pointer.add_id]

end Agave.Ed25519.SmallOrder.Execution

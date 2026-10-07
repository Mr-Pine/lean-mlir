import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructor
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory

/-! Execution of the exact inline initial-cache fragment of the serial table
constructor. Its instructions are projections of the imported original body,
including the compiler memcpy and the actual imported field-multiply call. -/
namespace Agave.Ed25519.Tables.SerialCacheExecution
open LeanMLIR.RIR
open SerialFieldMul SerialPoint SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] machine

def primitives (p : SerialConstructor.Primitives) : SerialConstructor.Primitives :=
  {p with call0 := SerialFieldMul.kernel.call}

/-- Exact original constants followed by its inline initial cache conversion. -/
abbrev phase (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals) : Func where
  Γ := SerialConstructor.kernel.Γ
  tRets := []
  n := 1
  blockTys := fun _ => []
  blockParams := fun _ => .nil
  hhasBlock := by decide
  hentry := rfl
  blocks := fun _ => {
    body := ((SerialConstructor.kernel.bb0 (primitives p) g).body.take 29) ++
      (((SerialConstructor.kernel.bb0 (primitives p) g).body.drop 37).take 80)
    exit := .ret .nil }

def cacheState (s : GlobalState) (out input constant : Pointer) : GlobalState :=
  let x := readLimbs s input
  let y := readLimbs s (input.add 40)
  let t := machine (readLimbs s (input.add 120)) (readLimbs s constant)
  let m := s.mem.storeAt (out.add 80) (s.mem.readAt (input.add 80) 320)
  let m := storeLimbs m (out.add 120) t
  let m := storeLimbs m out (addWord x y)
  {s with mem := storeLimbs m (out.add 40) (subWord y x)}

attribute [-simp] readLimbs_explicit in
theorem phase_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hg : SmallRange s.mem g.address0 40)
    (hoi : out.id ≠ input.id) (hog : out.id ≠ g.address0.id)
    (harg : E.args 1 = .value input) :
    (phase p g).runFrom (E[%35 := .value out]) ⟨0, by change 0 < 1; decide⟩ s =
      .value (.nil, cacheState s out input g.address0) := by
  have houtfits := hout.fits
  have hout0 := hout.fits_add (k := 0) (count := 8) (by decide)
  have hout8 := hout.fits_add (k := 8) (count := 8) (by decide)
  have hout16 := hout.fits_add (k := 16) (count := 8) (by decide)
  have hout24 := hout.fits_add (k := 24) (count := 8) (by decide)
  have hout32 := hout.fits_add (k := 32) (count := 8) (by decide)
  have hout40 := hout.fits_add (k := 40) (count := 8) (by decide)
  have hout48 := hout.fits_add (k := 48) (count := 8) (by decide)
  have hout56 := hout.fits_add (k := 56) (count := 8) (by decide)
  have hout64 := hout.fits_add (k := 64) (count := 8) (by decide)
  have hout72 := hout.fits_add (k := 72) (count := 8) (by decide)
  have hout80 := hout.fits_add (k := 80) (count := 8) (by decide)
  have hout88 := hout.fits_add (k := 88) (count := 8) (by decide)
  have hout96 := hout.fits_add (k := 96) (count := 8) (by decide)
  have hout104 := hout.fits_add (k := 104) (count := 8) (by decide)
  have hout112 := hout.fits_add (k := 112) (count := 8) (by decide)
  have hout120 := hout.fits_add (k := 120) (count := 8) (by decide)
  have hout128 := hout.fits_add (k := 128) (count := 8) (by decide)
  have hout136 := hout.fits_add (k := 136) (count := 8) (by decide)
  have hout144 := hout.fits_add (k := 144) (count := 8) (by decide)
  have hout152 := hout.fits_add (k := 152) (count := 8) (by decide)
  have houtfield0 := smallRange_add hout (k := 0) (count := 40) (by decide)
  have houtfield40 := smallRange_add hout (k := 40) (count := 40) (by decide)
  have houtfield80 := smallRange_add hout (k := 80) (count := 40) (by decide)
  have houtfield120 := smallRange_add hout (k := 120) (count := 40) (by decide)
  have hinfits := hin.fits
  have hin0 := hin.fits_add (k := 0) (count := 8) (by decide)
  have hin8 := hin.fits_add (k := 8) (count := 8) (by decide)
  have hin16 := hin.fits_add (k := 16) (count := 8) (by decide)
  have hin24 := hin.fits_add (k := 24) (count := 8) (by decide)
  have hin32 := hin.fits_add (k := 32) (count := 8) (by decide)
  have hin40 := hin.fits_add (k := 40) (count := 8) (by decide)
  have hin48 := hin.fits_add (k := 48) (count := 8) (by decide)
  have hin56 := hin.fits_add (k := 56) (count := 8) (by decide)
  have hin64 := hin.fits_add (k := 64) (count := 8) (by decide)
  have hin72 := hin.fits_add (k := 72) (count := 8) (by decide)
  have hin80 := hin.fits_add (k := 80) (count := 8) (by decide)
  have hin88 := hin.fits_add (k := 88) (count := 8) (by decide)
  have hin96 := hin.fits_add (k := 96) (count := 8) (by decide)
  have hin104 := hin.fits_add (k := 104) (count := 8) (by decide)
  have hin112 := hin.fits_add (k := 112) (count := 8) (by decide)
  have hin120 := hin.fits_add (k := 120) (count := 8) (by decide)
  have hin128 := hin.fits_add (k := 128) (count := 8) (by decide)
  have hin136 := hin.fits_add (k := 136) (count := 8) (by decide)
  have hin144 := hin.fits_add (k := 144) (count := 8) (by decide)
  have hin152 := hin.fits_add (k := 152) (count := 8) (by decide)
  have hinfield0 := smallRange_add hin (k := 0) (count := 40) (by decide)
  have hinfield40 := smallRange_add hin (k := 40) (count := 40) (by decide)
  have hinfield80 := smallRange_add hin (k := 80) (count := 40) (by decide)
  have hinfield120 := smallRange_add hin (k := 120) (count := 40) (by decide)
  have hout80full := houtfield80.fits
  have hin80full := hinfield80.fits
  have hgfits := hg.fits
  simp only [Pointer.add_zero] at hout0 hin0 houtfield0 hinfield0
  extract_state
  block_init
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
  have hgep := hin.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_load [harg]
  have hgep := hin.gep (k := 48) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
  have hgep := hin.gep (k := 56) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
  have hgep := hin.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
  have hgep := hin.gep (k := 72) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
  step_load [harg]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hin.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hin.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hin.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  have hgep := hin.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_load [harg]
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
  have hgep := hin.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  have hgep := hout.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_memcpy
  have hgep := hin.gep (k := 120) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  have hgep := hout.gep (k := 120) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_call using SerialFieldMul.kernel_call
  step_store
  have hgep := hout.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 48) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 56) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  have hgep := hout.gep (k := 72) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg]
  clear hgep
  step_store
  rw [BasicBlock.runBodyFrom_done (by exact Nat.le_refl 109)]
  change PoisonOr.value (Vals.nil, S) = _
  rw [hS]
  subst_vars
  simp (disch := first | assumption | ne_fact | fits_fact | disjoint_fact | omega)
    [cacheState, storeLimbs, readLimbs_explicit, readLimbs, Pointer.add_add,
      addWord, subWord, weakWord, biasedSubWord, bias, add_comm,
      mlir_mem, MemoryState.readAt_storeAt_disjoint]


/-- The loop's inline cache conversion is another exact source projection. -/
abbrev loopPhase (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals) : Func where
  Γ := SerialConstructor.kernel.Γ
  tRets := []
  n := 1
  blockTys := fun _ => []
  blockParams := fun _ => .nil
  hhasBlock := by decide
  hentry := rfl
  blocks := fun _ => {
    body := ((SerialConstructor.kernel.bb0 (primitives p) g).body.take 29) ++
      (((SerialConstructor.kernel.bb2 (primitives p)).body.drop 10).take 57)
    exit := .ret .nil }

abbrev loopInput (E : ⟪SerialConstructor.kernel.Γ⟫) (out input : Pointer) :
    ⟪SerialConstructor.kernel.Γ⟫ :=
  E[%32 := .value input, %33 := .value out,
    %118 := .value (input.add 40), %119 := .value (input.add 80),
    %120 := .value (input.add 120), %121 := .value (input.add 48),
    %122 := .value (input.add 56), %123 := .value (input.add 64),
    %124 := .value (input.add 72), %125 := .value (input.add 8),
    %126 := .value (input.add 16), %127 := .value (input.add 24),
    %128 := .value (input.add 32), %129 := .value (out.add 80),
    %130 := .value (out.add 120), %131 := .value (out.add 8),
    %132 := .value (out.add 16), %133 := .value (out.add 24),
    %134 := .value (out.add 32), %135 := .value (out.add 40),
    %136 := .value (out.add 48), %137 := .value (out.add 56),
    %138 := .value (out.add 64), %139 := .value (out.add 72)]

attribute [-simp] readLimbs_explicit in
theorem loopPhase_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (out input : Pointer)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : SmallRange s.mem input 160) (hg : SmallRange s.mem g.address0 40)
    (hoi : out.id ≠ input.id) (hog : out.id ≠ g.address0.id) :
    (loopPhase p g).runFrom (loopInput E out input) ⟨0, by change 0 < 1; decide⟩ s =
      .value (.nil, cacheState s out input g.address0) := by

  have houtfits := hout.fits
  have hout0 := hout.fits_add (k := 0) (count := 8) (by decide)
  have hout8 := hout.fits_add (k := 8) (count := 8) (by decide)
  have hout16 := hout.fits_add (k := 16) (count := 8) (by decide)
  have hout24 := hout.fits_add (k := 24) (count := 8) (by decide)
  have hout32 := hout.fits_add (k := 32) (count := 8) (by decide)
  have hout40 := hout.fits_add (k := 40) (count := 8) (by decide)
  have hout48 := hout.fits_add (k := 48) (count := 8) (by decide)
  have hout56 := hout.fits_add (k := 56) (count := 8) (by decide)
  have hout64 := hout.fits_add (k := 64) (count := 8) (by decide)
  have hout72 := hout.fits_add (k := 72) (count := 8) (by decide)
  have hout80 := hout.fits_add (k := 80) (count := 8) (by decide)
  have hout88 := hout.fits_add (k := 88) (count := 8) (by decide)
  have hout96 := hout.fits_add (k := 96) (count := 8) (by decide)
  have hout104 := hout.fits_add (k := 104) (count := 8) (by decide)
  have hout112 := hout.fits_add (k := 112) (count := 8) (by decide)
  have hout120 := hout.fits_add (k := 120) (count := 8) (by decide)
  have hout128 := hout.fits_add (k := 128) (count := 8) (by decide)
  have hout136 := hout.fits_add (k := 136) (count := 8) (by decide)
  have hout144 := hout.fits_add (k := 144) (count := 8) (by decide)
  have hout152 := hout.fits_add (k := 152) (count := 8) (by decide)
  have houtfield0 := smallRange_add hout (k := 0) (count := 40) (by decide)
  have houtfield40 := smallRange_add hout (k := 40) (count := 40) (by decide)
  have houtfield80 := smallRange_add hout (k := 80) (count := 40) (by decide)
  have houtfield120 := smallRange_add hout (k := 120) (count := 40) (by decide)
  have hinfits := hin.fits
  have hin0 := hin.fits_add (k := 0) (count := 8) (by decide)
  have hin8 := hin.fits_add (k := 8) (count := 8) (by decide)
  have hin16 := hin.fits_add (k := 16) (count := 8) (by decide)
  have hin24 := hin.fits_add (k := 24) (count := 8) (by decide)
  have hin32 := hin.fits_add (k := 32) (count := 8) (by decide)
  have hin40 := hin.fits_add (k := 40) (count := 8) (by decide)
  have hin48 := hin.fits_add (k := 48) (count := 8) (by decide)
  have hin56 := hin.fits_add (k := 56) (count := 8) (by decide)
  have hin64 := hin.fits_add (k := 64) (count := 8) (by decide)
  have hin72 := hin.fits_add (k := 72) (count := 8) (by decide)
  have hin80 := hin.fits_add (k := 80) (count := 8) (by decide)
  have hin88 := hin.fits_add (k := 88) (count := 8) (by decide)
  have hin96 := hin.fits_add (k := 96) (count := 8) (by decide)
  have hin104 := hin.fits_add (k := 104) (count := 8) (by decide)
  have hin112 := hin.fits_add (k := 112) (count := 8) (by decide)
  have hin120 := hin.fits_add (k := 120) (count := 8) (by decide)
  have hin128 := hin.fits_add (k := 128) (count := 8) (by decide)
  have hin136 := hin.fits_add (k := 136) (count := 8) (by decide)
  have hin144 := hin.fits_add (k := 144) (count := 8) (by decide)
  have hin152 := hin.fits_add (k := 152) (count := 8) (by decide)
  have hinfield0 := smallRange_add hin (k := 0) (count := 40) (by decide)
  have hinfield40 := smallRange_add hin (k := 40) (count := 40) (by decide)
  have hinfield80 := smallRange_add hin (k := 80) (count := 40) (by decide)
  have hinfield120 := smallRange_add hin (k := 120) (count := 40) (by decide)
  have hout80full := houtfield80.fits
  have hin80full := hinfield80.fits
  have hgfits := hg.fits
  simp only [Pointer.add_zero] at hout0 hin0 houtfield0 hinfield0

  extract_state
  block_init
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
  step_load
  step_load
  step_load
  step_load
  step_load
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
  step_load
  step_pure [weak_mul_nooverflow, weak_fold_nooverflow, weak_carry_add_nooverflow, final_add_nooverflow]
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
  step_memcpy
  step_call using SerialFieldMul.kernel_call
  step_store
  step_store
  step_store
  step_store
  step_store
  step_store
  step_store
  step_store
  step_store
  step_store
  rw [BasicBlock.runBodyFrom_done (by exact Nat.le_refl 86)]
  change PoisonOr.value (Vals.nil, S) = _
  rw [hS]
  subst_vars
  simp (disch := first | assumption | ne_fact | fits_fact | disjoint_fact | omega)
    [cacheState, storeLimbs, readLimbs_explicit, readLimbs, Pointer.add_add,
      addWord, subWord, weakWord, biasedSubWord, bias, add_comm,
      mlir_mem, MemoryState.readAt_storeAt_disjoint]

end Agave.Ed25519.Tables.SerialCacheExecution

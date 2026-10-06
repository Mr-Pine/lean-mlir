import SSA.Projects.Agave.Ed25519.Proof.NAF.BlockExecution

/-!
# Execution of the NAF entry block

The scalar word buffer, carry and cursor are established by the imported
entry block. Its memory conditions are the caller's legal ABI ranges and
separation; scratch allocation, zero padding and every interior pointer are
derived. The loop's digit correctness is not a premise.
-/
namespace Agave.Ed25519.NAF.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

private theorem modifyGet_run {α : Type} (f : GlobalState → α × GlobalState)
    (s : GlobalState) : (modifyGet f : EffectM α) s = .value (f s) := rfl

def clearedState (s : GlobalState) (out : Pointer) : GlobalState :=
  {s.alloca 40 with mem := (s.alloca 40).mem.storeAt out (0 : BitVec 2048)}

def paddedState (s : GlobalState) (out : Pointer) : GlobalState :=
  {clearedState s out with mem := (clearedState s out).mem.storeAt (s.allocaPtr.add 32#64) (0#64)}

def initializedState (s : GlobalState) (out : Pointer) (scalar : BitVec 256) : GlobalState :=
  {paddedState s out with mem := (paddedState s out).mem.storeAt s.allocaPtr scalar}

theorem scratch_cleared (s : GlobalState) (out : Pointer) :
    Buffer (clearedState s out).mem s.allocaPtr 40 :=
  (Buffer.alloca s 40 (by decide)).storeAt _ _

theorem scratch_padded (s : GlobalState) (out : Pointer) :
    Buffer (paddedState s out).mem s.allocaPtr 40 :=
  (scratch_cleared s out).storeAt _ _

theorem scratch_initialized (s : GlobalState) (out : Pointer) (scalar : BitVec 256) :
    Buffer (initializedState s out scalar).mem s.allocaPtr 40 :=
  (scratch_padded s out).storeAt _ _

theorem input_padded (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hinput : Buffer s.mem input 32) : Buffer (paddedState s out).mem input 32 :=
  ((hinput.alloca_existing hwf 40).storeAt _ _).storeAt _ _

theorem input_padded_read (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) :
    (paddedState s out).mem.readAt input 256 = scalar := by
  have hne := (GlobalState.ne_allocaPtr_of_fits hwf hinput.fits).symm
  have hpad : (Range.of (s.allocaPtr.add 32#64) 64).Disjoint (Range.of input 256) :=
    Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)
  unfold paddedState clearedState
  rw [MemoryState.readAt_storeAt_disjoint hpad,
    MemoryState.readAt_storeAt_disjoint hdisjoint,
    MemoryState.readAt_alloca hwf hinput.fits, hscalar]

/-- The real memcpy observes the original scalar, despite the preceding
allocation, output memset and padding-word store. -/
theorem initialize_copy (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) (env : ⟪Γ⟫) :
    Operation.memcpy (.value s.allocaPtr) (.value input) (.value 32#64) env (paddedState s out) =
      .value (env, initializedState s out scalar) := by
  have hne := (GlobalState.ne_allocaPtr_of_fits hwf hinput.fits).symm
  have hdst := (scratch_padded s out).fits_at 0 32 (by decide)
  simp only [Pointer.add_zero] at hdst
  have hcopy := run_memcpy (env := env) (s := paddedState s out)
    (show (32#64).toNat = 32 from rfl) (Range.disjoint_of_id_ne hne) hdst
    (input_padded s out input hwf hinput).fits
  rw [input_padded_read s out input scalar hwf hinput hdisjoint hscalar] at hcopy
  exact hcopy

/-- The output memset really establishes the zero digit array. -/
theorem initialized_digits_zero (s : GlobalState) (out : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) :
    (initializedState s out scalar).mem.readAt out 2048 = 0 := by
  have hne := (GlobalState.ne_allocaPtr_of_fits hwf hout.fits).symm
  have hcopy : (Range.of s.allocaPtr 256).Disjoint (Range.of out 2048) :=
    Range.disjoint_of_id_ne hne
  have hpad : (Range.of (s.allocaPtr.add 32#64) 64).Disjoint (Range.of out 2048) :=
    Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)
  unfold initializedState paddedState clearedState
  rw [MemoryState.readAt_storeAt_disjoint hcopy,
    MemoryState.readAt_storeAt_disjoint hpad,
    MemoryState.readAt_storeAt_self (hout.alloca_existing hwf 40).fits]

theorem initialized_scalar_buffer (s : GlobalState) (out : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) :
    (initializedState s out scalar).mem.readAt s.allocaPtr 320 = WordWindow.scalarBuffer scalar := by
  have hne := GlobalState.ne_allocaPtr_of_fits hwf hout.fits
  have hclear : (clearedState s out).mem.readAt s.allocaPtr 320 = 0 := by
    unfold clearedState
    rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hne),
      Memory.fresh_words_zero]
  have hb := scratch_cleared s out
  have hz : (paddedState s out).mem.readAt s.allocaPtr 320 = 0 := by
    have hp := MemoryState.readAt_add_storeAt (off := 32#64) hb.fits
      (hb.offset_noOverflow 32 (by decide)) (by decide : (32#64).toNat * 8 + 64 ≤ 320) (0#64)
    change ((clearedState s out).mem.storeAt (s.allocaPtr.add 32#64) (0#64)).readAt s.allocaPtr 320 = 0
    rw [hp, hclear]
    simp [LeanMLIR.RIR.Memory.spliceBits]
  exact Memory.copy_scalar_words (scratch_padded s out) hz scalar

def entryEnv5 (E : ⟪kernel5.Γ⟫) (s : GlobalState) : ⟪kernel5.Γ⟫ :=
  E[%0 := .value 1#32, %1 := .value 0#8, %2 := .value 256#64, %3 := .value 32#64,
    %4 := .value 0#64, %5 := .value 6#64, %6 := .value 63#64, %7 := .value 59#64,
    %8 := .value 8#64, %9 := .value 31#64, %10 := .value 1#64, %11 := .value 15#64,
    %12 := .value (-32 : BitVec 8), %13 := .value 5#64, %14 := .value 251#64,
    %15 := .value s.allocaPtr, %16 := .value (s.allocaPtr.add 32#64),
    %17 := .value 0#64, %18 := .value 0#64]

/-- Exact execution of the original allocation/memset/padding/memcpy entry
block, through its first carry/cursor edge. -/
theorem kernel5_entry_block (E : ⟪kernel5.Γ⟫) (s : GlobalState) (out input : Pointer)
    (scalar : BitVec 256) (hwf : s.WF) (hout : Buffer s.mem out 256)
    (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar)
    (harg0 : E.read (%arg0) = .value out) (harg1 : E.read (%arg1) = .value input) :
    kernel5.bb0.run kernel5.blockParams E s =
      .value ((entryEnv5 E s, .inr 1), initializedState s out scalar) := by
  change E.args 0 = .value out at harg0
  change E.args 1 = .value input at harg1
  have hzero (env : ⟪kernel5.Γ⟫) :
      Operation.memset (.value out) (.value 0#8) (.value 256#64) env (s.alloca 40) =
        .value (env, clearedState s out) :=
    Memory.zero_digits (s := s.alloca 40) (hout.alloca_existing hwf 40) env
  have hscale : Operation.gepInboundsIndex 1 (.value 32#64) = .value (32 : Int) := by decide +kernel
  have hgep := (scratch_cleared s out).gep 32 (by decide)
  simp only [Int.cast_ofNat_Int] at hgep
  have hfits := (scratch_cleared s out).fits_at 32 8 (by decide)
  have hstore (env : ⟪kernel5.Γ⟫) :
      Operation.store (τ := .bv 64) (.value (s.allocaPtr.add 32#64)) (.value 0#64) env
        (clearedState s out) = .value (env, paddedState s out) :=
    run_store (env := env) (s := clearedState s out) hfits rfl
  have hcopy := initialize_copy (Γ := kernel5.Γ) s out input scalar hwf hinput hdisjoint hscalar
  simp [BasicBlock.run, kernel5.bb0, entryEnv5,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    modifyGet_run, harg0, harg1, hzero, hscale, hgep, hstore,
    hcopy, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def entryEnv8 (E : ⟪kernel8.Γ⟫) (s : GlobalState) : ⟪kernel8.Γ⟫ :=
  E[%0 := .value 1#32, %1 := .value 0#8, %2 := .value 256#64, %3 := .value 32#64,
    %4 := .value 0#64, %5 := .value 6#64, %6 := .value 63#64, %7 := .value 56#64,
    %8 := .value 8#64, %9 := .value 255#64, %10 := .value 1#64, %11 := .value 127#64,
    %12 := .value 248#64, %13 := .value s.allocaPtr, %14 := .value (s.allocaPtr.add 32#64),
    %15 := .value 0#64, %16 := .value 0#64]

theorem kernel8_entry_block (E : ⟪kernel8.Γ⟫) (s : GlobalState) (out input : Pointer)
    (scalar : BitVec 256) (hwf : s.WF) (hout : Buffer s.mem out 256)
    (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar)
    (harg0 : E.read (%arg0) = .value out) (harg1 : E.read (%arg1) = .value input) :
    kernel8.bb0.run kernel8.blockParams E s =
      .value ((entryEnv8 E s, .inr 1), initializedState s out scalar) := by
  change E.args 0 = .value out at harg0
  change E.args 1 = .value input at harg1
  have hzero (env : ⟪kernel8.Γ⟫) :
      Operation.memset (.value out) (.value 0#8) (.value 256#64) env (s.alloca 40) =
        .value (env, clearedState s out) :=
    Memory.zero_digits (s := s.alloca 40) (hout.alloca_existing hwf 40) env
  have hscale : Operation.gepInboundsIndex 1 (.value 32#64) = .value (32 : Int) := by decide +kernel
  have hgep := (scratch_cleared s out).gep 32 (by decide)
  simp only [Int.cast_ofNat_Int] at hgep
  have hfits := (scratch_cleared s out).fits_at 32 8 (by decide)
  have hstore (env : ⟪kernel8.Γ⟫) :
      Operation.store (τ := .bv 64) (.value (s.allocaPtr.add 32#64)) (.value 0#64) env
        (clearedState s out) = .value (env, paddedState s out) :=
    run_store (env := env) (s := clearedState s out) hfits rfl
  have hcopy := initialize_copy (Γ := kernel8.Γ) s out input scalar hwf hinput hdisjoint hscalar
  simp [BasicBlock.run, kernel8.bb0, entryEnv8,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    modifyGet_run, harg0, harg1, hzero, hscale, hgep, hstore,
    hcopy, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

end Agave.Ed25519.NAF.RIR

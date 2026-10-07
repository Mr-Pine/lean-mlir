import SSA.Projects.Agave.Ed25519.Proof.NAF.TotalLoop

/-!
# Complete calls of the extracted NAF helpers

These theorems start at the function ABI and execute the imported entry block,
every loop iteration, and the callee frame removal. The resulting memory is
the source digit-store sequence over the caller's initially cleared output.
Scratch contents, interior bounds, carries, and termination are all derived.
-/
namespace Agave.Ed25519.NAF.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

/-- Erasing a callee frame commutes with the complete output store sequence. -/
theorem storeLoop_eraseFrom (width : Nat) (out : Pointer) (fuel pos : Nat)
    (state : State) (mem : MemoryState) (entry : Nat) :
    (Memory.storeLoop width out fuel pos state mem).eraseFrom entry =
      Memory.storeLoop width out fuel pos state (mem.eraseFrom entry) := by
  induction fuel generalizing pos state mem with
  | zero => rfl
  | succ fuel ih =>
      by_cases hpos : pos < 256
      · simp only [Memory.storeLoop, if_pos hpos]
        by_cases hdigit : (step width state).digit = 0
        · simp only [if_pos hdigit, ih]
        · simp only [if_neg hdigit, ih, MemoryState.eraseFrom_storeAt]
      · simp only [Memory.storeLoop, if_neg hpos]

/-- Both stores into the fresh scratch object disappear with its frame;
the output memset remains in the caller's memory. -/
theorem initializedState_erase (s : GlobalState) (out : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) :
    (initializedState s out scalar).mem.eraseFrom s.alloc.nextFreeBlock =
      s.mem.storeAt out (0 : BitVec 2048) := by
  unfold initializedState paddedState clearedState
  rw [MemoryState.eraseFrom_storeAt]
  rw [MemoryState.storeAt_eraseFrom_of_le (by exact Nat.le_refl _)]
  rw [MemoryState.eraseFrom_storeAt]
  rw [MemoryState.storeAt_eraseFrom_of_le (by exact Nat.le_refl _)]
  rw [MemoryState.eraseFrom_storeAt, GlobalState.eraseFrom_alloca, hwf.eraseFrom]

def finishedState (width : Nat) (s : GlobalState) (out : Pointer) (scalar : BitVec 256) :
    GlobalState :=
  {initializedState s out scalar with
    mem := Memory.storeLoop width out 256 0 ⟨scalar.toNat, 0⟩ (initializedState s out scalar).mem}

/-- The call increments the allocation counter once, deletes its scratch
allocation, and preserves the concrete output-store effects. -/
def returnedState (width : Nat) (s : GlobalState) (out : Pointer) (scalar : BitVec 256) :
    GlobalState :=
  {s.alloca 40 with mem :=
    Memory.storeLoop width out 256 0 ⟨scalar.toNat, 0⟩ (s.mem.storeAt out (0 : BitVec 2048))}

theorem finishedState_erase (width : Nat) (s : GlobalState) (out : Pointer)
    (scalar : BitVec 256) (hwf : s.WF) :
    {finishedState width s out scalar with mem :=
      (finishedState width s out scalar).mem.eraseFrom s.alloc.nextFreeBlock} =
        returnedState width s out scalar := by
  change {s.alloca 40 with mem :=
    (Memory.storeLoop width out 256 0 ⟨scalar.toNat, 0⟩
      (initializedState s out scalar).mem).eraseFrom s.alloc.nextFreeBlock} = _
  rw [storeLoop_eraseFrom, initializedState_erase s out scalar hwf]
  rfl

theorem returnedState_sourceDigits (width : Nat) (hw : Supported width) (s : GlobalState)
    (out : Pointer) (scalar : BitVec 256) (hout : Buffer s.mem out 256) (i : Fin 256) :
    (returnedState width s out scalar).mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (sourceDigits width scalar.toNat i) := by
  apply Memory.storeLoop_sourceDigits width hw scalar.toNat out _ (hout.storeAt _ _)
  exact MemoryState.readAt_storeAt_self hout.fits (0 : BitVec 2048)

def initialLoopEnv5 (E : ⟪kernel5.Γ⟫) (s : GlobalState) : ⟪kernel5.Γ⟫ :=
  (entryEnv5 E s)[%19 := .value 0#64]

theorem initialLoopEnv5_normalized (E : ⟪kernel5.Γ⟫) (s : GlobalState) :
    loopEnv5 (initialLoopEnv5 E s) s.allocaPtr 0 0 = initialLoopEnv5 E s := by
  apply loopEnv5_of_reads
  all_goals simp [initialLoopEnv5, entryEnv5, mlir_env]

/-- Complete execution of all imported blocks from the entry environment. -/
theorem kernel5_entry_run (E : ⟪kernel5.Γ⟫) (s : GlobalState) (out input : Pointer)
    (scalar : BitVec 256) (hwf : s.WF) (hout : Buffer s.mem out 256)
    (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar)
    (harg0 : E.read (%arg0) = .value out) (harg1 : E.read (%arg1) = .value input) :
    kernel5.runFrom E 0 s = .value (.nil, finishedState 5 s out scalar) := by
  rw [Func.runFrom_eq, show kernel5.blocks 0 = kernel5.bb0 from rfl,
    kernel5_entry_block E s out input scalar hwf hout hinput hdisjoint hscalar harg0 harg1]
  simp only [PoisonOr.value_bind, Func.continue]
  rw [kernel5_carry_entry]
  have hstart : (entryEnv5 E s)[%19 := (entryEnv5 E s).read (%17)] =
      initialLoopEnv5 E s := by
    simp [entryEnv5, initialLoopEnv5, mlir_env]
  rw [hstart, ← initialLoopEnv5_normalized E s]
  have hout' : Buffer (initializedState s out scalar).mem out 256 :=
    (((hout.alloca_existing hwf 40).storeAt _ _).storeAt _ _).storeAt _ _
  have harg : (initialLoopEnv5 E s).read (%arg0) = .value out := by
    simpa [initialLoopEnv5, entryEnv5, mlir_env] using harg0
  have hseparate := GlobalState.ne_allocaPtr_of_fits hwf hout.fits
  simpa only [Fin.val_zero, pow_zero, Nat.div_one, finishedState] using
    kernel5_loop_run 256 (initialLoopEnv5 E s) s.allocaPtr out scalar 0 0
      (initializedState s out scalar) (by decide) (scratch_initialized s out scalar)
      (initialized_scalar_buffer s out scalar hwf hout) hout' harg hseparate

/-- The exact extracted helper terminates from legal caller ranges. -/
theorem kernel5_run (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) :
    kernel5.run (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, finishedState 5 s out scalar) := by
  change kernel5.runFrom _ 0 s = _
  apply kernel5_entry_run _ s out input scalar hwf hout hinput hdisjoint hscalar
  all_goals rfl

/-- Actual `Func.call`, including the callee's frame erasure. The preconditions
are only caller memory validity, disjoint ABI ranges, and the scalar's read. -/
theorem kernel5_call (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) :
    kernel5.call (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, returnedState 5 s out scalar) := by
  rw [Func.call_of_run (kernel5_run s out input scalar hwf hout hinput hdisjoint hscalar),
    finishedState_erase 5 s out scalar hwf]

/-- The actual helper call returns every source NAF byte. -/
theorem kernel5_call_sourceDigits (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) :
    ∃ result, kernel5.call (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, result) ∧
      ∀ i : Fin 256, result.mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (sourceDigits 5 scalar.toNat i) := by
  exact ⟨returnedState 5 s out scalar,
    kernel5_call s out input scalar hwf hout hinput hdisjoint hscalar,
    returnedState_sourceDigits 5 (Or.inl rfl) s out scalar hout⟩

def initialLoopEnv8 (E : ⟪kernel8.Γ⟫) (s : GlobalState) : ⟪kernel8.Γ⟫ :=
  (entryEnv8 E s)[%17 := .value 0#64]

theorem initialLoopEnv8_normalized (E : ⟪kernel8.Γ⟫) (s : GlobalState) :
    loopEnv8 (initialLoopEnv8 E s) s.allocaPtr 0 0 = initialLoopEnv8 E s := by
  apply loopEnv8_of_reads
  all_goals simp [initialLoopEnv8, entryEnv8, mlir_env]

/-- Complete execution of all imported blocks from the entry environment. -/
theorem kernel8_entry_run (E : ⟪kernel8.Γ⟫) (s : GlobalState) (out input : Pointer)
    (scalar : BitVec 256) (hwf : s.WF) (hout : Buffer s.mem out 256)
    (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar)
    (harg0 : E.read (%arg0) = .value out) (harg1 : E.read (%arg1) = .value input) :
    kernel8.runFrom E 0 s = .value (.nil, finishedState 8 s out scalar) := by
  rw [Func.runFrom_eq, show kernel8.blocks 0 = kernel8.bb0 from rfl,
    kernel8_entry_block E s out input scalar hwf hout hinput hdisjoint hscalar harg0 harg1]
  simp only [PoisonOr.value_bind, Func.continue]
  rw [kernel8_carry_entry]
  have hstart : (entryEnv8 E s)[%17 := (entryEnv8 E s).read (%15)] =
      initialLoopEnv8 E s := by
    simp [entryEnv8, initialLoopEnv8, mlir_env]
  rw [hstart, ← initialLoopEnv8_normalized E s]
  have hout' : Buffer (initializedState s out scalar).mem out 256 :=
    (((hout.alloca_existing hwf 40).storeAt _ _).storeAt _ _).storeAt _ _
  have harg : (initialLoopEnv8 E s).read (%arg0) = .value out := by
    simpa [initialLoopEnv8, entryEnv8, mlir_env] using harg0
  have hseparate := GlobalState.ne_allocaPtr_of_fits hwf hout.fits
  simpa only [Fin.val_zero, pow_zero, Nat.div_one, finishedState] using
    kernel8_loop_run 256 (initialLoopEnv8 E s) s.allocaPtr out scalar 0 0
      (initializedState s out scalar) (by decide) (scratch_initialized s out scalar)
      (initialized_scalar_buffer s out scalar hwf hout) hout' harg hseparate

/-- The exact extracted helper terminates from legal caller ranges. -/
theorem kernel8_run (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) :
    kernel8.run (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, finishedState 8 s out scalar) := by
  change kernel8.runFrom _ 0 s = _
  apply kernel8_entry_run _ s out input scalar hwf hout hinput hdisjoint hscalar
  all_goals rfl

/-- Actual `Func.call`, including the callee's frame erasure. The preconditions
are only caller memory validity, disjoint ABI ranges, and the scalar's read. -/
theorem kernel8_call (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) :
    kernel8.call (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, returnedState 8 s out scalar) := by
  rw [Func.call_of_run (kernel8_run s out input scalar hwf hout hinput hdisjoint hscalar),
    finishedState_erase 8 s out scalar hwf]

/-- The actual helper call returns every source NAF byte. -/
theorem kernel8_call_sourceDigits (s : GlobalState) (out input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hout : Buffer s.mem out 256) (hinput : Buffer s.mem input 32)
    (hdisjoint : (Range.of out 2048).Disjoint (Range.of input 256))
    (hscalar : s.mem.readAt input 256 = scalar) :
    ∃ result, kernel8.call (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, result) ∧
      ∀ i : Fin 256, result.mem.readAt (out.add (BitVec.ofNat 64 i.val)) 8 =
        BitVec.ofInt 8 (sourceDigits 8 scalar.toNat i) := by
  exact ⟨returnedState 8 s out scalar,
    kernel8_call s out input scalar hwf hout hinput hdisjoint hscalar,
    returnedState_sourceDigits 8 (Or.inr rfl) s out scalar hout⟩

end Agave.Ed25519.NAF.RIR

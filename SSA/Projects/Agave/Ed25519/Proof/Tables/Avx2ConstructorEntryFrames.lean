import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorEntry
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorDouble
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorState

/-! Register preservation from the real constants and allocations through
serial packing and initial normalization. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.EntryFrames
open LeanMLIR.RIR
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem packing_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 400 480 E (Packing.result E) := by
  unfold Packing.result
  extract_lets
  iterate 80 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem normalization_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 480 505 E (CachePhases.normalizeResult E) := by
  unfold CachePhases.normalizeResult CachePhases.normalize1 CachePhases.normalize0
  extract_lets
  iterate 25 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem tight_frame (E : ⟪kernel.Γ⟫) (a : Packing.SerialPoint) :
    RegisterFrame 400 505 (TightPrefix.entry E a) (TightPrefix.result E a) :=
  ((packing_frame _).weaken (by decide) (by decide)).trans
    ((normalization_frame _).weaken (by decide) (by decide))

theorem result_loaded_frame (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    RegisterFrame 400 505 (Entry.loaded E s a) (Entry.result E s a) := by
  have h := tight_frame (Entry.loaded E s a) (Loads.point (Stack.state s 9).mem a)
  rw [Entry.packing_input_ready] at h
  exact h

theorem result_frame (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    RegisterFrame 352 505 (Constants.result E) (Entry.result E s a) :=
  ((Entry.register_frame E s a).weaken (by decide) (by decide)).trans
    ((result_loaded_frame E s a).weaken (by decide) (by decide))

theorem result_allocated_frame (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    RegisterFrame 361 505 (Entry.allocated E s) (Entry.result E s a) :=
  ((Loads.register_frame (Entry.allocated E s) (Stack.state s 9).mem a).weaken
    (by decide) (by decide)).trans
    ((result_loaded_frame E s a).weaken (by decide) (by decide))

theorem initial_pointers (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    Double.InitialPointers (Entry.result E s a) (State.slots s) := by
  have hf := result_allocated_frame E s a
  constructor
  · rw [hf.read (%352) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]
  · rw [hf.read (%353) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]
  · rw [hf.read (%354) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]
  · rw [hf.read (%355) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]
  · rw [hf.read (%356) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]
  · rw [hf.read (%357) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]
  · rw [hf.read (%358) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]
  · rw [hf.read (%359) (by decide)]
    simp [Entry.allocated, Stack.result, State.slots, mlir_env]

theorem table_read (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    (Entry.result E s a).read (%360) = .value (Stack.pointer s 8) := by
  rw [(result_allocated_frame E s a).read (%360) (by decide)]
  simp [Entry.allocated, Stack.result, mlir_env]

theorem arguments (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    (Entry.result E s a).args = E.args :=
  (result_frame E s a).arguments.trans (Constants.register_frame E).arguments

end Agave.Ed25519.Tables.Avx2Constructor.EntryFrames

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.EntryFrames.packing_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.EntryFrames.normalization_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.EntryFrames.result_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.EntryFrames.result_allocated_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.EntryFrames.initial_pointers,
      `Agave.Ed25519.Tables.Avx2Constructor.EntryFrames.table_read,
      `Agave.Ed25519.Tables.Avx2Constructor.EntryFrames.arguments] do
    let axioms ← collectAxioms endpoint
    for axiomName in axioms do
      unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "nonstandard axiom {axiomName} in {endpoint}"
    logInfo m!"standard-three audit passed: {endpoint}"

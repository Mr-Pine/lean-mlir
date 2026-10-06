/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRefinement16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootRun16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofLoop16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOffsets16

namespace AgaveLatticeHash.MLIR.BatchRefinement16
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
private theorem old0 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨67, rfl⟩ = V ⟨0, rfl⟩ := rfl
private theorem old1 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨68, rfl⟩ = V ⟨1, rfl⟩ := rfl
private theorem old2 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨69, rfl⟩ = V ⟨2, rfl⟩ := rfl
private theorem old3 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨70, rfl⟩ = V ⟨3, rfl⟩ := rfl
private theorem old4 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨71, rfl⟩ = V ⟨4, rfl⟩ := rfl
private theorem old5 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨72, rfl⟩ = V ⟨5, rfl⟩ := rfl
private theorem old6 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨73, rfl⟩ = V ⟨6, rfl⟩ := rfl
private theorem old7 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨74, rfl⟩ = V ⟨7, rfl⟩ := rfl
private theorem old8 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨75, rfl⟩ = V ⟨8, rfl⟩ := rfl
private theorem old9 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨76, rfl⟩ = V ⟨9, rfl⟩ := rfl
private theorem old10 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨77, rfl⟩ = V ⟨10, rfl⟩ := rfl
private theorem old11 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨78, rfl⟩ = V ⟨11, rfl⟩ := rfl
private theorem old12 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨79, rfl⟩ = V ⟨12, rfl⟩ := rfl
private theorem old13 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨80, rfl⟩ = V ⟨13, rfl⟩ := rfl
private theorem old14 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨81, rfl⟩ = V ⟨14, rfl⟩ := rfl
private theorem old15 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨82, rfl⟩ = V ⟨15, rfl⟩ := rfl
private theorem old16 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨83, rfl⟩ = V ⟨16, rfl⟩ := rfl
private theorem old17 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨84, rfl⟩ = V ⟨17, rfl⟩ := rfl
private theorem old18 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨85, rfl⟩ = V ⟨18, rfl⟩ := rfl
private theorem old19 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨86, rfl⟩ = V ⟨19, rfl⟩ := rfl
private theorem old20 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨87, rfl⟩ = V ⟨20, rfl⟩ := rfl
private theorem old21 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨88, rfl⟩ = V ⟨21, rfl⟩ := rfl
private theorem old22 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨89, rfl⟩ = V ⟨22, rfl⟩ := rfl
private theorem old23 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨90, rfl⟩ = V ⟨23, rfl⟩ := rfl
private theorem old24 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨91, rfl⟩ = V ⟨24, rfl⟩ := rfl
private theorem old25 (V : BatchHeader16.Input16.Valuation) :
    BatchHeader16.values16 V ⟨92, rfl⟩ = V ⟨25, rfl⟩ := rfl

attribute [local irreducible] BatchHeader16.values16

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- The nonroot edge preserves the exact CV and offsets and appends the
header's flags, lengths and frozen activity bytes. -/
theorem nonroot_forward (A : agave_batch_16.cfgCtx.Valuation)
    (cv : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16) :
    BatchTranspose16.nonrootTarget16
      (transposeInput A (headerInput16 A (headerTarget16 cv offsets).args)) =
    (⟨6, rfl, (headerTarget16 cv offsets).args.append
      [BatchHeader16.values16 (headerInput16 A (headerTarget16 cv offsets).args) ⟨43, rfl⟩,
       BatchHeader16.values16 (headerInput16 A (headerTarget16 cv offsets).args) ⟨37, rfl⟩,
       BatchHeader16.values16 (headerInput16 A (headerTarget16 cv offsets).args) ⟨33, rfl⟩]ₕ⟩ :
      SuccArgs agave_batch_16.cfgSigs) := by
  let V := headerInput16 A (headerTarget16 cv offsets).args
  change BatchTranspose16.nonrootTarget16 (transposeInput A V) = _
  calc
    _ = (⟨6, rfl, BatchHeader16.values16 V ⟨92, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨91, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨90, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨89, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨88, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨87, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨86, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨85, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨84, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨83, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨82, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨81, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨80, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨79, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨78, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨77, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨76, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨75, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨74, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨73, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨72, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨71, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨70, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨69, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨68, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨67, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨43, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨37, rfl⟩ ::ₕ BatchHeader16.values16 V ⟨33, rfl⟩ ::ₕ .nil⟩ : SuccArgs agave_batch_16.cfgSigs) := rfl
    _ = _ := by
      rw [old25, old24, old23, old22, old21, old20, old19, old18, old17, old16, old15, old14, old13, old12, old11, old10, old9, old8, old7, old6, old5, old4, old3, old2, old1, old0]
      rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- The root edge and retained-message copy preserve CV and decode the two
packed metadata vectors before entering the XOF header. -/
theorem root_forward (A : agave_batch_16.cfgCtx.Valuation)
    (cv : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16) :
    BatchRootCopy16.next5 (BatchRootRun16.input5 A
      (BatchTranspose16.rootTarget16
        (transposeInput A (headerInput16 A (headerTarget16 cv offsets).args))).args) =
    (⟨9, rfl, [A ⟨103, rfl⟩,
      Vector.ofFn (fun lane => PoisonOr.value (cv 7 lane)),
      Vector.ofFn (fun lane => PoisonOr.value (cv 6 lane)),
      Vector.ofFn (fun lane => PoisonOr.value (cv 5 lane)),
      Vector.ofFn (fun lane => PoisonOr.value (cv 4 lane)),
      Vector.ofFn (fun lane => PoisonOr.value (cv 3 lane)),
      Vector.ofFn (fun lane => PoisonOr.value (cv 2 lane)),
      Vector.ofFn (fun lane => PoisonOr.value (cv 1 lane)),
      Vector.ofFn (fun lane => PoisonOr.value (cv 0 lane)),
      BatchRootCopy16.words16 (BatchHeader16.values16
        (headerInput16 A (headerTarget16 cv offsets).args) ⟨37, rfl⟩),
      BatchRootCopy16.words16 (BatchHeader16.values16
        (headerInput16 A (headerTarget16 cv offsets).args) ⟨43, rfl⟩)]ₕ⟩ :
      SuccArgs agave_batch_16.cfgSigs) := by
  let V := headerInput16 A (headerTarget16 cv offsets).args
  calc
    _ = (⟨9, rfl, [A ⟨103, rfl⟩,
      BatchHeader16.values16 V ⟨74, rfl⟩,
      BatchHeader16.values16 V ⟨73, rfl⟩,
      BatchHeader16.values16 V ⟨72, rfl⟩,
      BatchHeader16.values16 V ⟨71, rfl⟩,
      BatchHeader16.values16 V ⟨70, rfl⟩,
      BatchHeader16.values16 V ⟨69, rfl⟩,
      BatchHeader16.values16 V ⟨68, rfl⟩,
      BatchHeader16.values16 V ⟨67, rfl⟩,
      BatchRootCopy16.words16 (BatchHeader16.values16 V ⟨37, rfl⟩),
      BatchRootCopy16.words16 (BatchHeader16.values16 V ⟨43, rfl⟩)]ₕ⟩ : SuccArgs agave_batch_16.cfgSigs) := rfl
    _ = _ := by
      rw [old7, old6, old5, old4, old3, old2, old1, old0]
      rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Metadata decoding suffices to identify the copied-root successor with the
semantic XOF-loop state at counter zero. -/
theorem root_target (A : agave_batch_16.cfgCtx.Valuation)
    (cv : CV (Lanes 16)) (offsets : Vector (BitVec 64) 16)
    (len flags : Vector Word 16)
    (hzero : A ⟨103, rfl⟩ = PoisonOr.value 0#64)
    (hlen : BatchRootCopy16.words16 (BatchHeader16.values16
      (headerInput16 A (headerTarget16 cv offsets).args) ⟨37, rfl⟩) = len.map PoisonOr.value)
    (hflags : BatchRootCopy16.words16 (BatchHeader16.values16
      (headerInput16 A (headerTarget16 cv offsets).args) ⟨43, rfl⟩) = flags.map PoisonOr.value) :
    BatchRootCopy16.next5 (BatchRootRun16.input5 A
      (BatchTranspose16.rootTarget16
        (transposeInput A (headerInput16 A (headerTarget16 cv offsets).args))).args) =
      BatchXofLoop16.rootTarget (fun w => Vector.ofFn (cv w)) len flags 0 := by
  rw [root_forward, hzero, hlen, hflags]
  simp only [BatchXofLoop16.rootTarget, Vector.map_ofFn, Function.comp_def]

/-- The byte-mask representation used by the actual update block is identical
to the frozen mask proved at the scalar-state header. -/
theorem activeBytes16_update (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :
    (activeBytes16 ms iteration).map PoisonOr.value =
      BatchUpdate16.activeBytes16 (fun lane => decide (iteration < AgaveBatchControl.rootIndex (ms lane).length)) := by
  apply Vector.ext
  intro i hi
  simp only [activeBytes16, BatchUpdate16.activeBytes16, Vector.getElem_map,
    Vector.getElem_ofFn]
  by_cases h : iteration < AgaveBatchControl.rootIndex (ms ⟨i, hi⟩).length <;>
    simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

/-- A root edge is taken exactly when every lane has reached its root block. -/
theorem activeMask16_zero_iff (ms : Fin 16 → AgaveConcrete.Message) (iteration : Nat) :
    activeMask16 ms iteration = 0 ↔
      ∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ iteration := by
  rw [activeMask16, BatchTranspose16.active16_zero_iff]
  simp only [activeBytes16, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn]
  constructor
  · intro h lane
    have hh := h lane
    by_contra hn
    have ha : iteration < AgaveBatchControl.rootIndex (ms lane).length := by omega
    simp [ha] at hh
  · intro h lane
    have ha : ¬ iteration < AgaveBatchControl.rootIndex (ms lane).length := by
      have := h lane
      omega
    simp [ha]

end AgaveLatticeHash.MLIR.BatchRefinement16

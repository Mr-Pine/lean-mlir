/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOuter8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootXof

namespace AgaveLatticeHash.MLIR.BatchExecution8
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)

noncomputable def finishState (entry current : GlobalState) (out : Pointer)
    (p : AgavePhysicalStaging.Store) (a : AgaveStaging.Value)
    (ms : Fin 8 → AgaveConcrete.Message) (t : Nat) (bytes : BitVec 4096) : GlobalState :=
  BatchXofLoop.accumulatedState
    {current with mem := current.mem.splice (BatchEntry.scratch entry 1) bytes}
    out (out.withOffset 32) (BatchRootXof.rootCV ms t) (BatchInputSuccessor.sizes ms t)
    (BatchInputSuccessor.flags ms t) (BatchReadInput8.columns p ms t)
    (BatchXofLoop.lowerSlice (CallerMemory.accumulatorWords a))
    (BatchXofLoop.upperSlice (CallerMemory.accumulatorWords a)) 32

/-- All premises of the compiled root-copy and 32-counter output loop follow
from the caller image and the outer loop's scratch-message invariant. -/
theorem root_run {entry current : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (hm : BatchMemory8 entry current) (ms : Fin 8 → AgaveConcrete.Message) (t : Nat)
    (hmsg : CompressionMessage current.mem (BatchEntry.scratch entry 0)
      (BatchReadInput8.columns p ms t)) :
    ∃ bytes : BitVec 4096,
      StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
        (BatchInputSuccessor.rootAt ms t)) current =
      .value (.nil, finishState entry current out p a ms t bytes) := by
  let bytes := readWord (hm.scratch 0)
  have hr : readWord? (BatchEntry.scratch entry 0) 4096 current.mem = some bytes :=
    readWord?_eq_some (hm.scratch 0) rfl
  refine ⟨bytes, ?_⟩
  have hsi (r : Fin 7) (i : Fin 16) : Fits current.mem (CompressionRound.schedulePtr sched r i) 64 := by
    apply hm.fits hrep.wf
    simpa only [CompressionRound.schedulePtr, CompressionRound.rowPtr, schedulePtr_two_geps] using
      scheduleGlobal_fits hrep.schedule r i
  have hsv (r : Fin 7) (i : Fin 16) : readWord? (CompressionRound.schedulePtr sched r i) 64 current.mem =
      some (BitVec.ofNat 64 (schedule r i).val) := by
    have hf : Fits entry.mem (CompressionRound.schedulePtr sched r i) 64 := by
      simpa only [CompressionRound.schedulePtr, CompressionRound.rowPtr, schedulePtr_two_geps] using
        scheduleGlobal_fits hrep.schedule r i
    rw [hm.read hrep.wf hf]
    simpa only [CompressionRound.schedulePtr, CompressionRound.rowPtr, schedulePtr_two_geps] using
      scheduleGlobal_read hrep.schedule r i
  have hf : Fits current.mem out 16384 := hm.fits hrep.wf hrep.accumulator.2.1
  have hra : readWord? out 16384 current.mem = some (packBits (CallerMemory.accumulatorWords a)) := by
    rw [hm.read hrep.wf hrep.accumulator.2.1]
    exact readWord?_eq_some hrep.accumulator.2.1 hrep.accumulator.2.2
  have hwrap : out.offset.toNat + 2048 ≤ 2^64 := by simp [hrep.out_zero]
  have hom : out.id ≠ (BatchEntry.scratch entry 1).id :=
    (BatchEntry.scratch_ne_input hrep.wf hrep.accumulator.2.1 1).symm
  have hms : (BatchEntry.scratch entry 1).id ≠ sched.id :=
    BatchEntry.scratch_ne_input hrep.wf hrep.schedule.1.2.1 1
  exact BatchRootXof.run entry src len out sched panic _ ms t current _ _ bytes hmsg
    (hm.scratch 1) hr hsi hsv hf hwrap hra hrep.output_schedule hom hms

set_option maxRecDepth 4096 in
/-- Actual entry execution, including both fresh scratch allocations and the
caller-length load, followed by the actual lifted CFG dispatcher. -/
theorem entry_run {entry : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (ms : Fin 8 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length) :
    StateT.run (agave_batch_8.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) entry =
    StateT.run (agave_batch_8.blocks.run (BatchReadInput8.ambient entry src len out sched panic ms)
      BatchEntry.header8) (BatchEntry.entryState entry) := by
  have hlens : CallerMemory.lengthWords 8 p =
      Vector.ofFn (fun lane : Fin 8 => BitVec.ofNat 64 (ms lane).length) := by
    apply Vector.ext
    intro i hi
    simp only [CallerMemory.lengthWords, Vector.getElem_ofFn, hlen]
  have hr : readWord? len 512 entry.mem = some (packBits
      (Vector.ofFn fun lane : Fin 8 => BitVec.ofNat 64 (ms lane).length)) := by
    rw [← hlens]
    exact readWord?_eq_some hrep.lengths.2.1 hrep.lengths.2.2
  have he := BatchEntry.entry8_denote entry hrep.wf src len out sched panic _
    hrep.source.2.1 hrep.lengths.2.1 hr hrep.schedule.1.1 hrep.panic
  unfold Cfg.denote
  apply EffectM.run_bind_of_value he

/-- Every represented full-width batch terminates normally in the actual
lifted CFG. The result retains its exact root time and byte-backed final
state for the observable LtHash readback theorem. -/
theorem terminates {entry : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (ms : Fin 8 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) :
    ∃ t rootState bytes, t ≤ 15 ∧
      (∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t) ∧
      BatchMemory8 entry rootState ∧
      CompressionMessage rootState.mem (BatchEntry.scratch entry 0) (BatchReadInput8.columns p ms t) ∧
      StateT.run (agave_batch_8.denote
        (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) entry =
      .value (.nil, finishState entry rootState out p a ms t bytes) := by
  obtain ⟨t, rootState, ht, hdone, hmem, hmsg, hexec⟩ :=
    BatchOuter8.reachesRoot_fromEntry hrep ms hms hstage
  obtain ⟨bytes, hroot⟩ := root_run hrep hmem ms t hmsg
  exact ⟨t, rootState, bytes, ht, hdone, hmem, hmsg, (entry_run hrep ms hlen).trans (hexec.trans hroot)⟩


/-- A normal denotation is witnessed by a finite run of the executable CFG
interpreter; the classical limit cannot create a successful execution. -/
theorem finite_eval_of_value {Γ : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty}
    (cfg : Cfg Γ rets) (V : Γ.Valuation) (s final : GlobalState)
    (result : HVector TyDenote.toType rets)
    (h : StateT.run (cfg.denote V) s = .value (result, final)) :
    ∃ fuel, Cfg.eval fuel cfg V s = some (.value (result, final)) := by
  rw [Cfg.run_denote] at h
  cases he : Fuel.limit (fun n => Cfg.eval n cfg V s) with
  | none => simp only [he, Fuel.force_none] at h; cases h
  | some r =>
    rw [he, Fuel.force_some] at h
    subst r
    exact Fuel.exists_of_limit_eq_some he

/-- The actual compiled batch has a finite, successful executable run on
all represented valid one-chunk lane buffers. -/
theorem terminates_eval {entry : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hrep : CallerMemory.Represents entry 8 src len out sched panic p a)
    (ms : Fin 8 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) :
    ∃ fuel final, Cfg.eval fuel agave_batch_8
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ) entry =
      some (.value (.nil, final)) := by
  obtain ⟨t, rootState, bytes, _, _, _, _, hrun⟩ := terminates hrep ms hlen hms hstage
  obtain ⟨fuel, heval⟩ := finite_eval_of_value _ _ _ _ _ hrun
  exact ⟨fuel, finishState entry rootState out p a ms t bytes, heval⟩

end AgaveLatticeHash.MLIR.BatchExecution8

/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOuter16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRootExecution16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchEntryPhysical16
import SSA.Projects.Agave.LatticeHash.MLIR.Execution

namespace AgaveLatticeHash.MLIR.BatchExecution16
open LeanMLIR SLLVM Firedancer BatchRefinement16 BatchXofLoop16
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A legal full sixteen-lane compiled invocation terminates normally. The
returned physical memory contains all thirty-two exact XOF reduction chunks. -/
theorem terminates {entry : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (ms : Fin 16 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) :
    ∃ final, Execution.BatchReturns .avx512 src len out entry final ∧
      Fits final.mem out 16384 ∧ ∃ t, t ≤ 15 ∧
      (∀ lane, AgaveBatchControl.rootIndex (ms lane).length ≤ t) ∧
      ∀ c, c < 32 → readWord? (outputPtr out c) 512 final.mem =
        some (packBits (BatchOutput16.sums32
          (outputSlice (CallerMemory.accumulatorWords a) c)
          (delta (rootCVAt16 ms t) (rootSizes16 ms t) (rootFlags16 ms t)
            (BatchTranspose16.columns16 (CallerMemory.rows16 p ms t)) c))) := by
  obtain ⟨t, rootState, _, ht, hdone, hm, hmsg, houter⟩ :=
    BatchOuter16.reachesRoot hc (batchMemory16_entry entry) ms hms hstage 0 15
      (fun lane => by have := AgaveBatchControl.rootIndex_lt16 _ (hms lane); omega)
  obtain ⟨final, hroot, hfit, hreads⟩ :=
    root_branch16 entry rootState src len out sched panic p a hc hm ms t hms hmsg
  refine ⟨final, ?_, hfit, t, ht, hdone, hreads⟩
  exact (physical_entry16 entry src len out sched panic p a hc ms hlen).trans
    (houter.trans hroot)

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

/-- The actual AVX512 CFG has a finite successful interpreter run. -/
theorem terminates_eval {entry : GlobalState} {src len out sched panic : Pointer}
    {p : AgavePhysicalStaging.Store} {a : AgaveStaging.Value}
    (hc : CallerMemory.Represents entry 16 src len out sched panic p a)
    (ms : Fin 16 → AgaveConcrete.Message)
    (hlen : ∀ lane, AgavePhysicalStaging.lengthAt p lane.val = (ms lane).length)
    (hms : ∀ lane, (ms lane).length ≤ 1024)
    (hstage : ∀ lane, AgaveBatchControl.ValidStaging (ms lane).length 1024
      (AgaveConcrete.bytes (ms lane)) (AgavePhysicalStaging.memoryAt p lane.val)) :
    ∃ fuel final, Cfg.eval fuel agave_batch_16
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ) entry =
      some (.value (.nil, final)) := by
  obtain ⟨final, hrun, _⟩ := terminates hc ms hlen hms hstage
  obtain ⟨fuel, heval⟩ := finite_eval_of_value _ _ _ _ _ hrun
  exact ⟨fuel, final, heval⟩

end AgaveLatticeHash.MLIR.BatchExecution16

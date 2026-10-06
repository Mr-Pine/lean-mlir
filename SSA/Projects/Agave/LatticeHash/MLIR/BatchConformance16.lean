/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchReadback16
import SSA.Projects.Agave.LatticeHash.MLIR.BatchExecution16
import SSA.Projects.Agave.LatticeHash.MLIR.CallerReference
import SSA.Projects.Agave.LatticeHash.MLIR.Execution

namespace AgaveLatticeHash.MLIR.BatchConformance16
open LeanMLIR SLLVM Firedancer
open AgaveStaging AgavePhysicalStaging

/-- Actual AVX512 batch execution terminates and every stored accumulator cell
is the retained-memory LtHash update. Caller validity supplies all load,
padding, schedule and loop preconditions. -/
theorem run_readback (base : GlobalState) (hb : base.WF)
    (p : Store) (s : Impl) (hr : Represents p s) (hf : p.count = 16)
    (hs : PendingOK s) (a : Value) :
    ∃ after, Execution.BatchReturns .avx512 (CallerMemory.ptr base 0)
      (CallerMemory.ptr base 1) (CallerMemory.ptr base 2)
      (CallerMemory.image base 16 p a) after ∧
      ∀ j : Fin 1024, readWord? ((CallerMemory.ptr base 2).withOffset
        (BitVec.ofNat 64 (2*j.val))) 16 after.mem =
        some (physicalUpdate 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p a j) := by
  have hc := CallerMemory.image_represents base hb 16 p a
  let ms : Fin 16 → AgaveConcrete.Message := fun lane =>
    AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hf) lane)
  obtain ⟨hlen, hms, hstage⟩ := CallerMemory.represented_messages 16 p s hr hf hs
  obtain ⟨after, hexec, hfit, t, _, hdone, hreads⟩ :=
    BatchExecution16.terminates hc ms hlen hms hstage
  refine ⟨after, hexec, ?_⟩
  exact BatchReadback16.finish_read after _ p a ms t hlen hms hstage hdone hfit
    (by simp [hc.out_zero]) hreads

/-- The actual 2048-byte AVX512 result is the fold of independent portable
BLAKE3 LtHash results for the sixteen represented short messages. -/
theorem run_portableLtHash (base : GlobalState) (hb : base.WF)
    (p : Store) (s : Impl) (hr : Represents p s) (hf : p.count = 16)
    (hs : PendingOK s) (a : Value) :
    let ms : Fin 16 → AgaveConcrete.Message := fun lane =>
      AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hf) lane)
    ∃ after, Execution.BatchReturns .avx512 (CallerMemory.ptr base 0)
      (CallerMemory.ptr base 1) (CallerMemory.ptr base 2)
      (CallerMemory.image base 16 p a) after ∧
      ∀ j : Fin 1024, readWord? ((CallerMemory.ptr base 2).withOffset
        (BitVec.ofNat 64 (2*j.val))) 16 after.mem =
        some (((List.finRange 16).foldl (fun z lane => plus z
          ((AgaveBlake3Reference.portableLtHash (ms lane)).getD zero)) a) j) := by
  obtain ⟨after, he, hrb⟩ := run_readback base hb p s hr hf hs a
  refine ⟨after, he, ?_⟩
  rw [CallerMemory.physicalUpdate_eq_portableLtHash 16 (by decide) _
    AgaveLattice.avx512_isTranspose p s hr hf hs a] at hrb
  exact hrb

/-- A concrete compiled invocation exists, starting from the closed caller
materialization; there is no execution or environmental existence premise. -/
theorem fullWidth_total (p : Store) (s : Impl) (hr : Represents p s)
    (hs : PendingOK s) (hf : p.count = 16) :
    Execution.FullWidthRun .avx512 p s.acc
      (physicalUpdate 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p s.acc) := by
  obtain ⟨after, he, hrb⟩ := run_readback CallerMemory.emptyState
    CallerMemory.emptyState_wf p s hr hf hs s.acc
  exact ⟨CallerMemory.emptyState, after, CallerMemory.emptyState_wf, he, hrb⟩

/-- Every normal compiled result on a represented full batch agrees with the
physical update, by determinism and independent output-memory readback. -/
theorem fullWidth_refines (p : Store) (s : Impl) (result : Value)
    (hr : Represents p s) (hs : PendingOK s) (hf : p.count = 16)
    (run : Execution.FullWidthRun .avx512 p s.acc result) :
    result = physicalUpdate 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p s.acc := by
  obtain ⟨base, after, hb, he, reads⟩ := run
  obtain ⟨expected, he', reads'⟩ := run_readback base hb p s hr hf hs s.acc
  have hstate : after = expected := by
    simp only [Execution.BatchReturns, Execution.Architecture.width] at he he'
    rw [he] at he'
    cases he'
    rfl
  subst expected
  funext j
  exact Option.some.inj ((reads j).symm.trans (reads' j))

end AgaveLatticeHash.MLIR.BatchConformance16

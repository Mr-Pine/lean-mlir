/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchReadback8
import SSA.Projects.Agave.LatticeHash.MLIR.CallerReference
import SSA.Projects.Agave.LatticeHash.MLIR.Execution

namespace AgaveLatticeHash.MLIR.BatchConformance8
open LeanMLIR SLLVM Firedancer
open AgaveStaging AgavePhysicalStaging

/-- Actual AVX2 batch execution terminates and every stored accumulator cell
is the retained-memory LtHash update. Caller validity supplies all load,
padding, schedule and loop preconditions. -/
theorem run_readback (base : GlobalState) (hb : base.WF)
    (p : Store) (s : Impl) (hr : Represents p s) (hf : p.count = 8)
    (hs : PendingOK s) (a : Value) :
    ∃ after, Execution.BatchReturns .avx2 (CallerMemory.ptr base 0)
      (CallerMemory.ptr base 1) (CallerMemory.ptr base 2)
      (CallerMemory.image base 8 p a) after ∧
      ∀ j : Fin 1024, readWord? ((CallerMemory.ptr base 2).withOffset
        (BitVec.ofNat 64 (2*j.val))) 16 after.mem =
        some (physicalUpdate 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p a j) := by
  have hc := CallerMemory.image_represents base hb 8 p a
  let ms : Fin 8 → AgaveConcrete.Message := fun lane =>
    AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hf) lane)
  obtain ⟨hlen, hms, hstage⟩ := CallerMemory.represented_messages 8 p s hr hf hs
  obtain ⟨t, rootState, bytes, _, hdone, hm, _, hexec⟩ :=
    BatchExecution8.terminates hc ms hlen hms hstage
  refine ⟨_, hexec, ?_⟩
  exact BatchReadback8.finish_read hc hm ms t hlen hms hstage hdone bytes

/-- The actual 2048-byte AVX2 result is the fold of independent portable
BLAKE3 LtHash results for the eight represented short messages. -/
theorem run_portableLtHash (base : GlobalState) (hb : base.WF)
    (p : Store) (s : Impl) (hr : Represents p s) (hf : p.count = 8)
    (hs : PendingOK s) (a : Value) :
    let ms : Fin 8 → AgaveConcrete.Message := fun lane =>
      AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hf) lane)
    ∃ after, Execution.BatchReturns .avx2 (CallerMemory.ptr base 0)
      (CallerMemory.ptr base 1) (CallerMemory.ptr base 2)
      (CallerMemory.image base 8 p a) after ∧
      ∀ j : Fin 1024, readWord? ((CallerMemory.ptr base 2).withOffset
        (BitVec.ofNat 64 (2*j.val))) 16 after.mem =
        some (((List.finRange 8).foldl (fun z lane => plus z
          ((AgaveBlake3Reference.portableLtHash (ms lane)).getD zero)) a) j) := by
  obtain ⟨after, he, hrb⟩ := run_readback base hb p s hr hf hs a
  refine ⟨after, he, ?_⟩
  rw [CallerMemory.physicalUpdate_eq_portableLtHash 8 (by decide) _
    AgaveLattice.avx2_isTranspose p s hr hf hs a] at hrb
  exact hrb

/-- A concrete compiled invocation exists, starting from the closed caller
materialization; there is no execution or environmental existence premise. -/
theorem fullWidth_total (p : Store) (s : Impl) (hr : Represents p s)
    (hs : PendingOK s) (hf : p.count = 8) :
    Execution.FullWidthRun .avx2 p s.acc
      (physicalUpdate 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p s.acc) := by
  obtain ⟨after, he, hrb⟩ := run_readback CallerMemory.emptyState
    CallerMemory.emptyState_wf p s hr hf hs s.acc
  exact ⟨CallerMemory.emptyState, after, CallerMemory.emptyState_wf, he, hrb⟩

/-- Every normal compiled result on a represented full batch agrees with the
physical update, by determinism and independent output-memory readback. -/
theorem fullWidth_refines (p : Store) (s : Impl) (result : Value)
    (hr : Represents p s) (hs : PendingOK s) (hf : p.count = 8)
    (run : Execution.FullWidthRun .avx2 p s.acc result) :
    result = physicalUpdate 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p s.acc := by
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

end AgaveLatticeHash.MLIR.BatchConformance8

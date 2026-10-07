import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkLoopStep

/-! The read-only bb8 setup establishes the complete dual-block loop invariant. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

/-- The bb8 setup preserves entry constants and establishes all loop pointers. -/
theorem bulk_initial_setup_loopInvariant (g : Globals) (E : Env program.Γ)
    (chain scratch cache : Pointer) (s : Spec.State)
    (he : BulkInitialEntryReady g E) (h : BulkInitialReady E chain scratch cache)
    (ht : BulkTailSecondConstants E cache)
    (hm : E.read (%80) = .value 18446744073709551615#64) :
    BulkLoopInvariant g (bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s))
      chain scratch cache := by
  have hf := bulk_initial_setup_frame E chain scratch cache s
  obtain ⟨hc, hp⟩ := bulk_initial_setup_pointers E chain scratch cache s h
  refine ⟨he.of_frame hf, hp, hc, ?_, (hf.read (%80)).trans hm⟩
  exact ⟨(hf.read (%82)).trans ht.cache,
    (hf.read (%3)).trans ht.eight, (hf.read (%79)).trans ht.limit,
    (hf.read (%36)).trans ht.rot14, (hf.read (%37)).trans ht.rot18,
    (hf.read (%38)).trans ht.rot41, (hf.read (%39)).trans ht.rot28,
    (hf.read (%40)).trans ht.rot34, (hf.read (%41)).trans ht.rot39⟩

/-- Exact bb8 execution supplies the initial state and invariant required at bb9. -/
theorem bulk_initial_setup_loop_entry (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain scratch cache : Pointer) (s : Spec.State) (index pairs : BitVec 64)
    (he : BulkInitialEntryReady g E) (h : BulkInitialReady E chain scratch cache)
    (ht : BulkTailSecondConstants E cache)
    (hm : E.read (%80) = .value 18446744073709551615#64)
    (hi : E.read (%86) = .value index) (hp : E.read (%90) = .value pairs)
    (hc : SmallRange mem.mem chain 64) (hs : SmallRange mem.mem scratch 128)
    (hcache : SmallRange mem.mem cache 640) (hr : InitialChainReads mem.mem chain s) :
    let E' := bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s)
    ExecTrace (program g) 1 E 8 mem E' 9 mem ∧
      BulkLoopInvariant g E' chain scratch cache ∧
      BulkOuterReady E' s index pairs ∧ RegFrame 321 359 E E' := by
  exact ⟨ExecTrace.single (bulk_initial_setup_run E mem chain scratch cache s h hc hs hcache hr),
    bulk_initial_setup_loopInvariant g E chain scratch cache s he h ht hm,
    bulk_initial_setup_ready E chain scratch cache s index pairs hi hp,
    bulk_initial_setup_frame E chain scratch cache s⟩

end Agave.Ed25519.SHA512.Execution.Avx2

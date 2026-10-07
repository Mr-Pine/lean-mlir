import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkExecution
import SSA.Projects.RIR.Run.Call

/-! Exact arbitrary-count scalar call and caller-visible compression effects. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open ScalarFull

def bulkArgs (chain data : Pointer) (count : BitVec 64) : Vals [.ptr, .ptr, .bv 64] :=
  .cons (.value chain) (.cons (.value data) (.cons (.value count) .nil))

def bulkAfter (state : GlobalState) (chain data : Pointer) (count : BitVec 64) : GlobalState :=
  {state with mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * count.toNat)))}

theorem warm_scalar_bulk_run (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hg : CompressionReady cg state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    (program p (readyGlobals cg)).run (bulkArgs chain data count) state =
      .value (.nil, bulkAfter state chain data count) := by
  rw [Func.run_runFrom_eq]
  apply warm_scalar_bulk_of_ready p cg _ state chain data count hg hc hd hb <;> rfl

/-- The scalar source allocates no frame, so actual call cleanup preserves
its exact single-store result for every live count. -/
theorem warm_scalar_bulk_call (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hwf : state.WF) (hg : CompressionReady cg state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    (program p (readyGlobals cg)).call (bulkArgs chain data count) state =
      .value (.nil, bulkAfter state chain data count) := by
  apply Func.call_eq_of_run_eq (warm_scalar_bulk_run p cg state chain data count hg hc hd hb)
  · exact hwf.storeAt
  · rfl

theorem warm_scalar_bulk_call_ready (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hwf : state.WF) (hg : CompressionCallReady cg state chain data)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    (program p (readyGlobals cg)).call (bulkArgs chain data count) state =
      .value (.nil, bulkAfter state chain data count) ∧
    CompressionStoreEffect cg state (bulkAfter state chain data count) chain
      (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * count.toNat))) ∧
    CompressionCallReady cg (bulkAfter state chain data count) chain data := by
  refine ⟨warm_scalar_bulk_call p cg state chain data count hwf hg.globals hc hd hb, ?_, ?_⟩
  · obtain ⟨old, hlegal, hp⟩ := hg.globals.cache
    refine ⟨old, old, hlegal, hp, CacheTransition.refl old, ?_, Nat.le_refl _⟩
    rw [cache_store_same cg state.mem old hp]
    rfl
  · exact ⟨CompressionReady.storeAt cg state chain _ hg.globals hg.chainConstants hg.chainCache,
      hg.chainConstants, hg.chainCache, hg.dataCache⟩

/-- The exact `CompressContractUnder` conclusion at every invocation whose
cache selects the scalar source. It is conditional only on that branch byte;
all source arithmetic, reads, loop iterations, stores and returns are proved. -/
theorem warm_scalar_bulk_contract (p : Primitives) (cg : CompressionGlobals)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hwf : state.WF) (hg : CompressionCallReady cg state chain data)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (_hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))))
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8) :
    ∃ after,
      (program p (readyGlobals cg)).call (.cons (.value chain) (.cons (.value data)
        (.cons (.value count) .nil))) state = .value (.nil, after) ∧
      CompressionStoreEffect cg state after chain
        (Spec.compression.run (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat))) ∧
      CompressionReady cg after := by
  obtain ⟨he, hm, hr⟩ := warm_scalar_bulk_call_ready p cg state chain data count hwf hg hc hd hb
  exact ⟨bulkAfter state chain data count, he, hm, hr.globals⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk

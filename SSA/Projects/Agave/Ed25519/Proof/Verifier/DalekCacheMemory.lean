import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts

/-!
# AVX2 cache memory boundary

The exact initializer is now preserved in
`MLIR/generated/agave_initialize_avx2_cache.{ll,mlir}`, with extraction hashes in
`avx2-cache-manifest.json`. The original verifier artifact contains only its
declaration. Its body executes three CPUID inline assemblies, conditionally calls
XGETBV, computes a Boolean, zero-extends it to a byte, performs a monotonic atomic
store to the cache, and returns the Boolean.

The current RIR importer rejects both `llvm.inline_asm` and atomic stores. Thus
this module does NOT claim an imported execution theorem for that body. Instead,
`CacheStoreExecution` states the remaining one-call execution equation explicitly,
and the theorem below derives the caller's frame and cache-byte facts from it.
No synthesized replacement function is installed as the compiled initializer.

Hardware feature-detection accuracy is not a premise here: `CacheContract` permits
any cache byte, since both backend refinements have the same result.
Termination and the sequential memory effect of the real hardware-dependent call
are still required by `CacheStoreExecution`. Concurrent atomic-event semantics
are outside this memory model.
-/

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR

namespace Avx2Cache

/-- The sequential state after the initializer's sole caller-visible store. -/
def stored (state : GlobalState) (cache : Pointer) (enabled : Bool) : GlobalState :=
  { state with mem := state.mem.storeAt cache (choiceByte enabled) }

/-- Explicit unresolved execution boundary for the actual compiled initializer.
The feature result is arbitrary; this premise does not assert CPUID accuracy.
It does assert return, the byte store, and absence of other sequential effects.
It must not be confused with a proved execution of the extracted MLIR body. -/
def CacheStoreExecution (call : Vals [] → EffectM (Vals [.bv 1]))
    (cache : Pointer) : Prop :=
  ∀ (state : GlobalState), state.WF → ReadBytes state cache 1 255 →
    ∃ enabled : Bool,
      call .nil state =
        .value (.cons (.value (if enabled then 1 else 0)) .nil,
          stored state cache enabled)

/-- A one-byte store preserves allocation sizes and all disjoint reads. -/
theorem stored_frame (state : GlobalState) (cache : Pointer) (enabled : Bool)
    (hwf : state.WF) : OutputFrame state (stored state cache enabled) cache 1 := by
  refine ⟨hwf.storeAt, ?_, ?_⟩
  · intro q n hq
    exact hq.storeAt cache (choiceByte enabled)
  · intro q width hd
    exact MemoryState.readAt_storeAt_disjoint hd.symm (choiceByte enabled)

/-- The stored byte can be read back whenever the old cache byte was live. -/
theorem stored_read (state : GlobalState) (cache : Pointer) (enabled : Bool)
    (hlive : Reduce64.Execution.SmallRange state.mem cache 1) :
    ReadBytes (stored state cache enabled) cache 1 (if enabled then 1 else 0) := by
  refine ⟨hlive.storeAt cache (choiceByte enabled), ?_⟩
  exact MemoryState.readAt_storeAt_self hlive.fits (choiceByte enabled)

/-- The Dalek cache contract needs only the frame, not the normalized byte
proved by `stored_read`. The hardware-dependent call equation remains explicit. -/
theorem contract_of_store_execution
    (call : Vals [] → EffectM (Vals [.bv 1])) (cache : Pointer)
    (hexec : CacheStoreExecution call cache) : CacheContract call cache := by
  intro state hwf hcache
  obtain ⟨enabled, hcall⟩ := hexec state hwf hcache
  exact ⟨stored state cache enabled, (if enabled then 1 else 0),
    hcall, stored_frame state cache enabled hwf⟩

end Avx2Cache
end Agave.Ed25519.Verifier.Execution.Dalek

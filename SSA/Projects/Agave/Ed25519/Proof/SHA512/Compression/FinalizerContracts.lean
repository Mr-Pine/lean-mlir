import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ContextContract

/-! Cold-capable SHA finalizer ABI. This is a separate interface from the
legacy exact-store ABI; no unrelated caller memory guarantee is weakened.
The sole additional observable write is its declared one-byte dispatch cache.
-/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge

/-- The public output and input context have provenance separate from the
dispatcher cache. The finalizer's internal chain/block buffers are fresh. -/
structure CompressionFinalizerReady (g : CompressionGlobals) (state : GlobalState)
    (dst ctx : Pointer) : Prop where
  «globals» : CompressionReady g state
  dstConstants : dst.id ≠ g.constants
  dstCache : dst.id ≠ g.cache
  ctxCache : ctx.id ≠ g.cache

/-- The reducer-specific readiness parameter is unchanged. In addition the
compressor's table/cache readiness is required at this particular invocation.
An initialized cache is not required, so the first invocation is included. -/
def CacheFramedScalarFromSha512ContractUnder (g : CompressionGlobals)
    (ready : GlobalState → Pointer → Prop)
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (sha : Sha512Model) : Prop :=
  ∀ (state : GlobalState) (dst ctx : Pointer) (completed pending : Bytes),
    state.WF → ready state dst → CompressionFinalizerReady g state dst ctx →
    SmallRange state.mem dst 32 →
    ContextRepresents sha state.mem ctx completed pending →
    (Range.of dst 256).Disjoint (Range.of ctx 1664) →
    ∃ after,
      call (.cons (.value dst) (.cons (.value ctx) .nil)) state =
        .value (.nil, after) ∧
      CacheFramedStoreEffect g state after dst
        (digestScalarBytes (sha.digest (completed ++ pending))) ∧
      CompressionReady g after

/-- The old exact-store finalizer result follows on warm invocations. Its
unchanged-memory promise is recovered as equality of whole memory maps. -/
theorem scalarFromSha512_warm (g : CompressionGlobals)
    (ready : GlobalState → Pointer → Prop)
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (sha : Sha512Model)
    (hcall : CacheFramedScalarFromSha512ContractUnder g ready call sha)
    (state : GlobalState) (dst ctx : Pointer) (completed pending : Bytes)
    (hwf : state.WF) (hr : ready state dst)
    (hg : CompressionFinalizerReady g state dst ctx) (hwarm : CacheWarm g state)
    (hd : SmallRange state.mem dst 32)
    (hc : ContextRepresents sha state.mem ctx completed pending)
    (hdis : (Range.of dst 256).Disjoint (Range.of ctx 1664)) :
    ∃ after,
      call (.cons (.value dst) (.cons (.value ctx) .nil)) state =
        .value (.nil, after) ∧
      StoreEffect state after dst (digestScalarBytes (sha.digest (completed ++ pending))) := by
  obtain ⟨after, he, hm, _⟩ := hcall state dst ctx completed pending hwf hr hg hd hc hdis
  exact ⟨after, he, hm.to_storeEffect hwarm⟩

/-- Both cold and warm calls supply the same scalar to every subsequent
Boolean consumer. The cache may differ, but no scalar-output assumption is
introduced: it follows directly from the finalizer's declared memory effect. -/
theorem scalarFromSha512_boolean_observation (g : CompressionGlobals)
    (ready : GlobalState → Pointer → Prop)
    (call : Vals [.ptr, .ptr] → EffectM (Vals [])) (sha : Sha512Model)
    (hcall : CacheFramedScalarFromSha512ContractUnder g ready call sha)
    (state : GlobalState) (dst ctx : Pointer) (completed pending : Bytes)
    (hwf : state.WF) (hr : ready state dst)
    (hg : CompressionFinalizerReady g state dst ctx)
    (hd : SmallRange state.mem dst 32)
    (hc : ContextRepresents sha state.mem ctx completed pending)
    (hdis : (Range.of dst 256).Disjoint (Range.of ctx 1664))
    (observe : BitVec 256 → Bool) :
    ∃ after,
      call (.cons (.value dst) (.cons (.value ctx) .nil)) state =
        .value (.nil, after) ∧
      CacheFramedStoreEffect g state after dst
        (digestScalarBytes (sha.digest (completed ++ pending))) ∧
      observe (after.mem.readAt dst 256) =
        observe (digestScalarBytes (sha.digest (completed ++ pending))) := by
  obtain ⟨after, he, hm, _⟩ := hcall state dst ctx completed pending hwf hr hg hd hc hdis
  exact ⟨after, he, hm, hm.boolean_observation hd.fits observe⟩

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

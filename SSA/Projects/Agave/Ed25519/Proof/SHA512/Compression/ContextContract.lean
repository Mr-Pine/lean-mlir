import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Effects

/-! Invocation-local compression ABI, permitting only the declared cache
initialization and chaining-state writes. The imported dispatcher still needs
an execution proof of this obligation. -/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge

/-- The complete caller-facing compression ABI, including a zero-length
slice and arbitrary live complete-block slices. The count is the original
64-bit ABI argument; no separate no-overflow or message-validity premise is
assumed. The live small-allocation bound supplies the required arithmetic
bounds. Instantiating `compress` with `Spec.compression` makes the output
the independently defined fold of the FIPS eighty-round block operation.

The entire call performs one legal cache transition and one chaining-state
store, regardless of how many scalar or two-block AVX iterations it executes. -/
def CompressContractUnder (g : CompressionGlobals)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression) : Prop :=
  ∀ (state : GlobalState) (chain data : Pointer) (count : BitVec 64),
    state.WF → CompressionCallReady g state chain data →
    SmallRange state.mem chain 64 →
    SmallRange state.mem data (128 * count.toNat) →
    (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))) →
    ∃ after,
      call (.cons (.value chain) (.cons (.value data)
        (.cons (.value count) .nil))) state = .value (.nil, after) ∧
      CompressionStoreEffect g state after chain
        (compress.run (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat))) ∧
      CompressionReady g after

/-- The compiler's 128-byte block stride fits without wrapping as a
consequence of the actual input allocation, including for a zero block count. -/
theorem compress_count_bound (state : GlobalState) (data : Pointer) (count : BitVec 64)
    (h : SmallRange state.mem data (128 * count.toNat)) : count.toNat < 2 ^ 56 := by
  have hb := h.offset_lt
  norm_num at hb ⊢
  omega

/-- Local single-block ABI for the concrete dispatcher. The table/cache
invariant is required at this invocation, preserved at return, and independent
of any assertion that SHA-512 has already been computed correctly. -/
def OneBlockCompressContractUnder (g : CompressionGlobals)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression) : Prop :=
  ∀ (state : GlobalState) (chain data : Pointer),
    state.WF → CompressionCallReady g state chain data →
    SmallRange state.mem chain 64 → SmallRange state.mem data 128 →
    (Range.of chain 512).Disjoint (Range.of data 1024) →
    ∃ after,
      call (.cons (.value chain) (.cons (.value data)
        (.cons (.value 1#64) .nil))) state = .value (.nil, after) ∧
      CompressionStoreEffect g state after chain
        (compress.run (state.mem.readAt chain 512) (readBytes state.mem data 128)) ∧
      CompressionReady g after

/-- Finalization uses the same bulk-compressor implementation at count one. -/
theorem oneBlock_of_compress_under (g : CompressionGlobals)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression)
    (h : CompressContractUnder g call compress) :
    OneBlockCompressContractUnder g call compress := by
  intro state chain data hwf hr hc hd hdis
  simpa using h state chain data 1#64 hwf hr hc hd hdis

/-- Warm bulk invocations recover exactly the old chain-store effect for
the full block fold. This includes the challenge prefix/bulk call. -/
theorem compress_warm (g : CompressionGlobals)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression)
    (hcall : CompressContractUnder g call compress)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hwf : state.WF) (hr : CompressionCallReady g state chain data)
    (hwarm : CacheWarm g state)
    (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data (128 * count.toNat))
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat)))) :
    ∃ after,
      call (.cons (.value chain) (.cons (.value data)
        (.cons (.value count) .nil))) state = .value (.nil, after) ∧
      StoreEffect state after chain
        (compress.run (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat))) ∧
      CompressionReady g after := by
  obtain ⟨after, he, hm, hready⟩ := hcall state chain data count hwf hr hc hd hdis
  exact ⟨after, he, CacheFramedStoreEffect.to_storeEffect hm hwarm, hready⟩

/-- Restricting the cold-capable obligation to a warm invocation recovers
exactly the old single-store postcondition, with no additional memory writes. -/
theorem oneBlockCompress_warm (g : CompressionGlobals)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression)
    (hcall : OneBlockCompressContractUnder g call compress)
    (state : GlobalState) (chain data : Pointer)
    (hwf : state.WF) (hr : CompressionCallReady g state chain data)
    (hwarm : CacheWarm g state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data 128)
    (hdis : (Range.of chain 512).Disjoint (Range.of data 1024)) :
    ∃ after,
      call (.cons (.value chain) (.cons (.value data)
        (.cons (.value 1#64) .nil))) state = .value (.nil, after) ∧
      StoreEffect state after chain
        (compress.run (state.mem.readAt chain 512) (readBytes state.mem data 128)) ∧
      CompressionReady g after := by
  obtain ⟨after, he, hm, hready⟩ := hcall state chain data hwf hr hc hd hdis
  exact ⟨after, he, CacheFramedStoreEffect.to_storeEffect hm hwarm, hready⟩

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

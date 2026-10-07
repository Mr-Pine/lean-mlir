import SSA.Projects.Agave.Ed25519.Proof.SHA512.Padding
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ExecutionProgram

/-! Local contracts for the two external symbols in the imported finalizer.
Neither contract assumes anything about finalization or the challenge result. -/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

/-- Only a single 128-byte block is needed by either finalization branch.
The memory effect is exactly the updated eight native chaining words. -/
def OneBlockCompressContract
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression) : Prop :=
  ∀ (state : GlobalState) (chain data : Pointer),
    state.WF → SmallRange state.mem chain 64 → SmallRange state.mem data 128 →
    (Range.of chain 512).Disjoint (Range.of data 1024) →
    ∃ after,
      call (.cons (.value chain) (.cons (.value data)
        (.cons (.value 1#64) .nil))) state = .value (.nil, after) ∧
      StoreEffect state after chain
        (compress.run (state.mem.readAt chain 512) (readBytes state.mem data 128))

/-- Exact wide scalar reduction ABI: the address-order digest is read as one
little-endian 512-bit integer and reduced modulo the Ed25519 subgroup order.
All memory other than the output bytes is preserved, including internal frame
cleanup. The allocation counter may advance. -/
def ReduceWideContract (call : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (state : GlobalState) (dst src : Pointer),
    state.WF → SmallRange state.mem dst 32 → SmallRange state.mem src 64 →
    (Range.of dst 256).Disjoint (Range.of src 512) →
    ∃ after,
      call (.cons (.value dst) (.cons (.value src) .nil)) state =
        .value (.nil, after) ∧
      StoreEffect state after dst (digestScalarBytes (state.mem.readAt src 512))

/-- The existing incremental ABI entails precisely the restricted contract
used by this wrapper, without an assumption about a whole digest. -/
theorem oneBlock_of_compress
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression)
    (h : CompressContract call (Agave.Ed25519.SHA512.model compress)) :
    OneBlockCompressContract call compress := by
  intro state chain data hwf hc hd hdisjoint
  simpa [Agave.Ed25519.SHA512.model] using
    h state chain data 1#64 hwf hc hd hdisjoint (by decide) (by decide)

/-- Readback of the reduction contract in its mathematical integer form. -/
theorem reduceWide_output
    (call : Vals [.ptr, .ptr] → EffectM (Vals []))
    (h : ReduceWideContract call) (state : GlobalState) (dst src : Pointer)
    (hwf : state.WF) (hdst : SmallRange state.mem dst 32)
    (hsrc : SmallRange state.mem src 64)
    (hdisjoint : (Range.of dst 256).Disjoint (Range.of src 512)) :
    ∃ after,
      call (.cons (.value dst) (.cons (.value src) .nil)) state =
        .value (.nil, after) ∧
      (after.mem.readAt dst 256).toNat =
        (state.mem.readAt src 512).toNat % Agave.Ed25519.Bridge.subgroupOrder ∧
      after.WF := by
  obtain ⟨after, hc, he⟩ := h state dst src hwf hdst hsrc hdisjoint
  refine ⟨after, hc, ?_, he.wellFormed hwf⟩
  rw [he.memory, MemoryState.readAt_storeAt_self hdst.fits, digestScalarBytes_toNat]

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

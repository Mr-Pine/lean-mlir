import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdCallerFrame
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionContext

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge

theorem compress_blocks_cold (cg : SHA512Finalization.CompressionGlobals) (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : SHA512Finalization.CompressContractUnder cg compressCall compress)
    (s : GlobalState) (ctx src : Pointer) (q : BitVec 64) (completed blocks : Bytes)
    (hwf : s.WF) (hc : ChainRepresents (Agave.Ed25519.SHA512.model compress) s.mem ctx completed)
    (hsrc : SmallRange s.mem src (128 * q.toNat))
    (hbytes : readBytes s.mem src (128 * q.toNat) = blocks)
    (hlen : blocks.length = 128 * q.toNat)
    (hchain : (Range.of (ctx.add 128) 512).Disjoint
      (Range.of src (8 * (128 * q.toNat))))
    (hcounter : (Range.of (ctx.add 192) 128).Disjoint
      (Range.of src (8 * (128 * q.toNat))))
    (hq : 0 < q.toNat) (hqbound : q.toNat < 2 ^ 56)
    (hcount : completed.length / 128 + q.toNat < 2 ^ 128)
    (hready : SHA512Finalization.CompressionReady cg s)
    (hctxK : ctx.id ≠ cg.constants) (hctxCache : ctx.id ≠ cg.cache)
    (hsrcCache : src.id ≠ cg.cache) :
    ∃ after,
      compressCall (.cons (.value (ctx.add 128)) (.cons (.value src)
        (.cons (.value q) .nil))) (advanceCount s ctx q) = .value (.nil, after) ∧
      SHA512Finalization.CacheOutputEffect cg (advanceCount s ctx q) after (ctx.add 128)
        (compress.run (compress.run initialWords completed) blocks) ∧
      ChainRepresents (Agave.Ed25519.SHA512.model compress) after.mem ctx (completed ++ blocks) ∧ after.WF ∧ SHA512Finalization.CompressionReady cg after := by
  let counted := advanceCount s ctx q
  have hcounted : counted.WF := GlobalState.WF.storeAt hwf
  have hlive : SmallRange counted.mem ctx 208 := hc.live.storeAt _ _
  have hs : SmallRange counted.mem src (128 * q.toNat) := hsrc.storeAt _ _
  have hdc : (Range.of (ctx.add 192) 128).Disjoint (Range.of (ctx.add 128) 512) :=
    smallRange_disjoint_offsets hc.live (i := 192) (countI := 16)
      (j := 128) (countJ := 64) (by decide) (by decide) (Or.inr (by decide))
  have hrchain : counted.mem.readAt (ctx.add 128) 512 = compress.run initialWords completed := by
    dsimp only [counted, advanceCount]
    rw [MemoryState.readAt_storeAt_disjoint hdc]
    exact hc.chaining
  have hrdata : readBytes counted.mem src (128 * q.toNat) = blocks := by
    dsimp only [counted, advanceCount]
    rw [readBytes_storeAt_disjoint _ _ _ _ _ hsrc hcounter]
    exact hbytes
  have hrCounted : SHA512Finalization.CompressionReady cg counted :=
    SHA512Finalization.CompressionReady.storeAt cg s (ctx.add 192) _ hready hctxK hctxCache
  obtain ⟨after, hcall, heRaw, hrAfter⟩ := hcompress counted (ctx.add 128) src q hcounted
    ⟨hrCounted, hctxK, hctxCache, hsrcCache⟩
    (smallRange_add hlive (k := 128) (count := 64) (by decide)) hs hchain
  have heffect := heRaw.cacheOutput hrAfter hctxCache
  rw [hrchain, hrdata] at heffect
  refine ⟨after, hcall, heffect, ?_, heffect.wellFormed hrCounted hcounted, hrAfter⟩
  have hwhole : blocks.length % 128 = 0 := by rw [hlen]; omega
  have hprior := hc.whole
  refine ⟨heffect.smallRange ctx 208 hctxCache hlive, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · rw [heffect.output hctxCache (context_chain_fits hlive)]
    exact (compress.append _ _ _ hc.whole hwhole).symm
  · rw [heffect.read (ctx.add 192) 128 hctxCache hdc.symm]
    dsimp only [counted, advanceCount]
    rw [MemoryState.readAt_storeAt_self (context_blocks_fits hc.live), BitVec.toNat_add,
      BitVec.toNat_setWidth, hc.blockCount]
    have hq128 : q.toNat < 2 ^ 128 := by omega
    rw [Nat.mod_eq_of_lt hq128, Nat.mod_eq_of_lt hcount]
    simp only [List.length_append, hlen]
    omega


end Agave.Ed25519.Verifier.Execution.Challenge

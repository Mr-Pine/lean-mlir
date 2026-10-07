import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdChallengePrefix
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdFullCall
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionLinked

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge Agave.Ed25519.Bridge.Challenge
open SHA512Finalization (CompressionGlobals CompressionReady CacheFrame CacheOutputEffect
  ColdFinalizerReady ScalarFromSha512ColdContract ChallengeCallerRegions)

/-- Invocation readiness for the real challenge call. It names the SHA cache
and explicitly separates every caller region consumed after this call, plus
both immutable scalar-reduction constants. -/
structure ColdChallengeReady (cg : CompressionGlobals) (rg : ScalarWide.Globals)
    (s : GlobalState) (out key signature message : Pointer) : Prop where
  compression : CompressionReady cg s
  reduction : ScalarWide.Ready rg s out
  outputCache : out.id ≠ cg.cache
  outputConstants : out.id ≠ cg.constants
  keyCache : key.id ≠ cg.cache
  signatureCache : signature.id ≠ cg.cache
  messageCache : message.id ≠ cg.cache
  reduceRCache : rg.address0.id ≠ cg.cache
  reduceRRCache : rg.address1.id ≠ cg.cache

set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

/-- Compose the actual challenge prefix and bb7 context copy with the cold
finalizer contract. No premise describes execution of the entire challenge. -/
theorem challenge_run_cold (cg : CompressionGlobals) (rg : ScalarWide.Globals)
    (p : Primitives) (g : Globals) (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : SHA512Finalization.CompressContractUnder cg p.sha512Compress compress)
    (hscalar : ScalarFromSha512ColdContract cg rg p.scalarFromSha512 compress)
    (E : Env program.Γ) (s : GlobalState) (dst aptr rptr msg : Pointer)
    (n : BitVec 64) (r a : BitVec 256) (message : Bytes)
    (h0 : E.read (%arg0) = .value dst) (h1 : E.read (%arg1) = .value aptr)
    (h2 : E.read (%arg2) = .value rptr) (h3 : E.read (%arg3) = .value msg)
    (h4 : E.read (%arg4) = .value n) (hwf : s.WF)
    (hr : ColdChallengeReady cg rg s dst aptr rptr msg)
    (hout : SmallRange s.mem dst 32) (ha : SmallRange s.mem aptr 32)
    (hsig : SmallRange s.mem rptr 32) (hinput : SmallRange s.mem msg n.toNat)
    (har : s.mem.readAt aptr 256 = a) (hrr : s.mem.readAt rptr 256 = r)
    (hm : readBytes s.mem msg n.toNat = message)
    (hiv : SmallRange s.mem g.address0 64)
    (hivr : s.mem.readAt g.address0 512 = initialWords) :
    ∃ after,
      (program p g).runFrom E 0 s = .value (.nil, after) ∧
      CacheFrame cg (s.mem.storeAt dst
        (digestScalarBytes (Agave.Ed25519.SHA512.digest compress (transcript r a message))))
        (after.mem.eraseFrom s.alloc.nextFreeBlock) ∧
      s.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock := by
  obtain ⟨F, t, completed, pending, hprefix, hregs, hctx, hbytes, ho, ht, hframe, hready⟩ :=
    challenge_reaches_final_cold cg p g compress hcompress E s dst aptr rptr msg n r a message
      h0 h1 h2 h3 h4 hwf hout ha hsig hinput har hrr hm hiv hivr
      hr.compression hr.outputCache hr.messageCache
  let copied : GlobalState :=
    ⟨t.alloc, t.mem.storeAt (finalSlot s) (t.mem.readAt (contextSlot s) 1664)⟩
  have hcopied : ContextRepresents (Agave.Ed25519.SHA512.model compress) copied.mem
      (finalSlot s) completed pending :=
    ContextRepresents.copy _ t.mem (contextSlot s) (finalSlot s) completed pending hctx ho.copy
  have hfcopy : CacheFrame cg s.mem (copied.mem.eraseFrom s.alloc.nextFreeBlock) :=
    hframe.internal_store (finalSlot s) (t.mem.readAt (contextSlot s) 1664) (final_internal s)
  have hcache := hr.compression.cache_lt hwf
  have hcopyCache : (finalSlot s).id ≠ cg.cache := by
    have hi := final_internal s
    intro h; have := congrArg BlockId.id h; omega
  have hcallReady : ColdFinalizerReady cg rg copied dst (finalSlot s) :=
    ⟨CompressionReady.of_cacheFrame cg s copied s.alloc.nextFreeBlock hfcopy hr.compression,
      SHA512Finalization.scalarReady_of_cacheFrame cg rg s copied dst s.alloc.nextFreeBlock hfcopy
        hr.reduction hr.reduceRCache hr.reduceRRCache,
      hr.outputCache, hr.outputConstants, hcopyCache, hr.reduceRCache, hr.reduceRRCache⟩
  obtain ⟨after, hcall, he⟩ := hscalar copied dst (finalSlot s) completed pending ht.storeAt
    hcallReady (ho.output.storeAt _ _) hcopied
  have hlast := final_block p g F t after dst (contextSlot s) (finalSlot s)
    hregs.output hregs.context hregs.scratch hregs.bytes hctx.live.fits ho.copy.fits
    (Or.inl (final_ne_context s)) hcall
  refine ⟨after, hprefix.trans hlast, ?_, ?_⟩
  · have heframe := he.memory.eraseFrom s.alloc.nextFreeBlock hcache
    rw [MemoryState.eraseFrom_storeAt] at heframe
    have htotal := (hfcopy.storeAt dst _ hr.outputCache).trans heframe
    simpa only [← hbytes, Agave.Ed25519.SHA512.model] using htotal
  · have hentry : s.alloc.nextFreeBlock ≤ t.alloc.nextFreeBlock := by
      have hlocal := ht.lt hctx.live.fits.mem
      have hi := context_internal s
      omega
    exact hentry.trans he.counter

/-- Exact challenge-call boundary with the designated cache exception.
All caller regions used by the downstream Boolean path are explicitly
preserved, while the scalar is still the digest of original R || A || message. -/
theorem challenge_call_cold (cg : CompressionGlobals) (rg : ScalarWide.Globals)
    (p : Primitives) (g : Globals) (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : SHA512Finalization.CompressContractUnder cg p.sha512Compress compress)
    (hscalar : ScalarFromSha512ColdContract cg rg p.scalarFromSha512 compress)
    (s : GlobalState) (dst aptr rptr msg : Pointer) (n : BitVec 64)
    (r a : BitVec 256) (message : Bytes) (hwf : s.WF)
    (hr : ColdChallengeReady cg rg s dst aptr rptr msg)
    (hout : SmallRange s.mem dst 32) (ha : SmallRange s.mem aptr 192)
    (hsig : SmallRange s.mem rptr 64) (hinput : SmallRange s.mem msg n.toNat)
    (har : s.mem.readAt aptr 256 = a) (hrr : s.mem.readAt rptr 256 = r)
    (hm : readBytes s.mem msg n.toNat = message)
    (hiv : SmallRange s.mem g.address0 64) (hivr : s.mem.readAt g.address0 512 = initialWords)
    (hda : (Range.of dst 256).Disjoint (Range.of aptr 1536))
    (hdr : (Range.of dst 256).Disjoint (Range.of rptr 512))
    (hdm : (Range.of dst 256).Disjoint (Range.of msg (8 * n.toNat))) :
    ∃ after,
      (program p g).call (challengeArgs dst aptr rptr msg n) s = .value (.nil, after) ∧
      CacheOutputEffect cg s after dst
        (digestScalarBytes (Agave.Ed25519.SHA512.digest compress (transcript r a message))) ∧
      ChallengeCallerRegions s after aptr rptr msg n.toNat ∧
      after.mem.readAt dst 256 =
        digestScalarBytes (Agave.Ed25519.SHA512.digest compress (transcript r a message)) ∧ after.WF := by
  let args := challengeArgs dst aptr rptr msg n
  obtain ⟨last, hrun, hframe, hcounter⟩ := challenge_run_cold cg rg p g compress hcompress hscalar
    (Env.init args.get) s dst aptr rptr msg n r a message
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get])
    (by simp [args, challengeArgs, mlir_env, Env.init, Vals.get]) hwf hr hout
    (smallRange_mono ha (by decide)) (smallRange_mono hsig (by decide)) hinput har hrr hm hiv hivr
  have hrun' : (program p g).run args s = .value (.nil, last) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  let after : GlobalState := {last with mem := last.mem.eraseFrom s.alloc.nextFreeBlock}
  have he : CacheOutputEffect cg s after dst
      (digestScalarBytes (Agave.Ed25519.SHA512.digest compress (transcript r a message))) :=
    ⟨hframe, hcounter⟩
  exact ⟨after, Func.call_of_run hrun', he,
    he.challenge_regions aptr rptr msg n.toNat ha hsig hinput
      hr.keyCache hr.signatureCache hr.messageCache hda hdr hdm,
    he.output hr.outputCache hout.fits, he.wellFormed hr.compression hwf⟩

/-- Replace the scalar-from-SHA symbol by the imported finalizer with its
actual linked wide reducer, retaining only compressor and reducer execution
obligations at their own local interfaces. -/
noncomputable def coldLinkedPrimitives (rg : ScalarWide.Globals)
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])) : Primitives :=
  ⟨compressCall, (SHA512Finalization.program (ScalarWide.finalizationPrimitives rg compressCall)).call⟩

theorem coldLinked_finalizer_contract (cg : CompressionGlobals) (rg : ScalarWide.Globals)
    (compress : Agave.Ed25519.SHA512.Compression)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (hcompress : SHA512Finalization.CompressContractUnder cg call compress)
    (hreduce : ScalarWide.ExecutionObligation rg) :
    ScalarFromSha512ColdContract cg rg (coldLinkedPrimitives rg call).scalarFromSha512 compress :=
  SHA512Finalization.linked_finalizer_cold cg rg compress call
    (SHA512Finalization.oneBlock_of_compress_under cg call compress hcompress) hreduce

end Agave.Ed25519.Verifier.Execution.Challenge

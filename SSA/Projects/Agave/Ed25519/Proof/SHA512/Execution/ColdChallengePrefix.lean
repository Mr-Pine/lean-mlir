import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdChallengeSuffix
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionEntry

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open SHA512Finalization (CompressionGlobals CompressionReady CacheFrame)

set_option maxRecDepth 24000
set_option maxHeartbeats 1800000

theorem challenge_reaches_final_cold (cg : CompressionGlobals) (p : Primitives) (g : Globals) (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : SHA512Finalization.CompressContractUnder cg p.sha512Compress compress)
    (E : Env program.Γ) (s : GlobalState) (dst aptr rptr msg : Pointer)
    (n : BitVec 64) (r a : BitVec 256) (message : Bytes)
    (h0 : E.read (%arg0) = .value dst) (h1 : E.read (%arg1) = .value aptr)
    (h2 : E.read (%arg2) = .value rptr) (h3 : E.read (%arg3) = .value msg)
    (h4 : E.read (%arg4) = .value n) (hwf : s.WF)
    (hout : SmallRange s.mem dst 32) (ha : SmallRange s.mem aptr 32)
    (hr : SmallRange s.mem rptr 32) (hinput : SmallRange s.mem msg n.toNat)
    (har : s.mem.readAt aptr 256 = a) (hrr : s.mem.readAt rptr 256 = r)
    (hm : readBytes s.mem msg n.toNat = message)
    (hiv : SmallRange s.mem g.address0 64)
    (hivr : s.mem.readAt g.address0 512 = initialWords)
    (hready : CompressionReady cg s) (houtCache : dst.id ≠ cg.cache)
    (hmsgCache : msg.id ≠ cg.cache) :
    ColdReachesFinal cg p g (Agave.Ed25519.SHA512.model compress) E 0 s dst (contextSlot s) (finalSlot s)
      (transcript r a message) s.alloc.nextFreeBlock s.mem := by
  change E.args 0 = .value dst at h0
  let ctx := contextSlot s
  let copy := finalSlot s
  let es := entryState s r a
  let ee := entryEnv E g s n
  have hlen : message.length = n.toNat := by rw [← hm, readBytes_length]
  have hewf : es.WF := entry_wf hwf
  have heout : OutputResources es dst copy := ⟨entry_live hwf hout, entry_final_live s⟩
  have hect : ContextRepresents (Agave.Ed25519.SHA512.model compress) es.mem ctx []
      (bytesOf (n := 32) r ++ bytesOf (n := 32) a) := entry_context (Agave.Ed25519.SHA512.model compress) s hwf r a
  have heinput : SmallRange es.mem msg n.toNat := entry_live hwf hinput
  have hemessage : readBytes es.mem msg n.toNat = message :=
    (entry_readBytes s hwf r a msg n.toNat hinput).trans hm
  have heregs : FinalRegisters ee dst ctx copy := by
    constructor <;> simp [ee, entryEnv, ctx, copy, mlir_env, h0]
  have hne : ctx.id ≠ msg.id := context_ne_caller hwf hinput
  have hcc : copy.id ≠ ctx.id := final_ne_context s
  have hoc : dst.id ≠ copy.id := (final_ne_caller hwf hout).symm
  have hctx : s.alloc.nextFreeBlock ≤ ctx.id.id := context_internal s
  have hcopy : s.alloc.nextFreeBlock ≤ copy.id.id := final_internal s
  have heframe : es.mem.eraseFrom s.alloc.nextFreeBlock = s.mem := entry_frame s hwf r a
  have hcache := hready.cache_lt hwf
  have hconstants := hready.constants_lt hwf
  have hctxCache : ctx.id ≠ cg.cache := by
    intro h; have := congrArg BlockId.id h; omega
  have hcopyCache : copy.id ≠ cg.cache := by
    intro h; have := congrArg BlockId.id h; omega
  have hctxK : ctx.id ≠ cg.constants := by
    intro h; have := congrArg BlockId.id h; omega
  have heReady : CompressionReady cg es :=
    CompressionReady.of_frame cg s es s.alloc.nextFreeBlock heframe hready
  have hentry := entry_block p g (Agave.Ed25519.SHA512.model compress) E s rptr aptr r a n h2 h1 h4 hwf hr ha hrr har hiv hivr
  by_cases hshort : n.toNat < 64
  · have hcontext : ContextRepresents (Agave.Ed25519.SHA512.model compress) (shortState es ctx msg n).mem ctx []
        ((bytesOf (n := 32) r ++ bytesOf (n := 32) a) ++ message) := by
      have h := append_pending (Agave.Ed25519.SHA512.model compress) es.mem ctx msg []
        (bytesOf (n := 32) r ++ bytesOf (n := 32) a) message hect
        (by simpa [hlen] using heinput) (by simpa [hlen] using hemessage)
        (by simp only [List.length_append, length_bytesOf]; omega)
      simpa [shortState, hlen, length_bytesOf] using h
    have hregs : FinalRegisters (shortEnv ee ctx n) dst ctx copy := by
      rcases heregs with ⟨h0', h18, h19, h16⟩
      constructor <;> simp_all [shortEnv, mlir_env]
    have hframe : (shortState es ctx msg n).mem.eraseFrom s.alloc.nextFreeBlock = s.mem :=
      erase_internal_store _ _ _ _ _ (erase_internal_store _ _ _ _ _ heframe hctx) hctx
    refine ⟨shortEnv ee ctx n, shortState es ctx msg n, [],
      ((bytesOf (n := 32) r ++ bytesOf (n := 32) a) ++ message), ?_, hregs, hcontext,
      ?_, (heout.store _ _).store _ _, hewf.storeAt.storeAt,
      by rw [hframe]; exact CacheFrame.refl cg s.mem hready.cache,
      CompressionReady.of_frame cg s _ s.alloc.nextFreeBlock hframe hready⟩
    · rw [hentry, if_pos hshort]
      rw [short_block p g ee es ctx msg n heregs.context
        (by simpa [ee, entryEnv, mlir_env] using h3)
        (by simpa [ee, entryEnv, mlir_env] using h4)
        (by simp [ee, entryEnv, mlir_env]) (by simp [ee, entryEnv, mlir_env])
        (by simp [ee, entryEnv, ctx, mlir_env]) hect.live heinput hshort hne]
    · simp [transcript, List.append_assoc]
  · have hlong : 64 ≤ n.toNat := by omega
    let filled := firstFill es ctx msg
    have hfillLive : SmallRange filled.mem ctx 208 := hect.live.storeAt _ _
    have hfillChain : ChainRepresents (Agave.Ed25519.SHA512.model compress) filled.mem ctx [] :=
      hect.chain.buffer_store 64 64 (by decide) (es.mem.readAt msg 512)
    have hmsg64 : SmallRange es.mem msg 64 := smallRange_mono heinput hlong
    have hread64 : readBytes es.mem msg 64 = message.take 64 := by
      rw [← hemessage, readBytes_take _ _ _ _ hlong]
    have hreadRA : readBytes es.mem ctx 64 = bytesOf (n := 32) r ++ bytesOf (n := 32) a := by
      simpa only [List.length_append, length_bytesOf] using hect.pendingBytes
    have hfirstRead : readBytes filled.mem ctx 128 = firstBlock r a message := by
      have h := readBytes_copy_append es.mem msg ctx 64 64 hmsg64
        (smallRange_mono hect.live (by decide))
      rw [hreadRA, hread64] at h
      simpa [filled, firstFill, firstBlock, List.append_assoc] using h
    have hdchain : (Range.of (ctx.add 128) 512).Disjoint (Range.of ctx 1024) := by
      simpa using smallRange_disjoint_offsets hfillLive
        (i := 128) (countI := 64) (j := 0) (countJ := 128)
        (by decide) (by decide) (Or.inr (by decide))
    have hdcounter : (Range.of (ctx.add 192) 128).Disjoint (Range.of ctx 1024) := by
      simpa using smallRange_disjoint_offsets hfillLive
        (i := 192) (countI := 16) (j := 0) (countJ := 128)
        (by decide) (by decide) (Or.inr (by decide))
    obtain ⟨afterFirst, hcall, he, hc', hwf', hrFirst⟩ := compress_blocks_cold cg p.sha512Compress compress hcompress
      filled ctx ctx 1#64 [] (firstBlock r a message) hewf.storeAt hfillChain
      (smallRange_mono hfillLive (by decide)) hfirstRead
      (firstBlock_length r a message (by omega)) hdchain hdcounter
      (by decide) (by decide) (by simp)
      (CompressionReady.storeAt cg es (ctx.add 64#64) _ heReady hctxK hctxCache)
      hctxK hctxCache hctxCache
    simp only [List.nil_append] at hc'
    have hremainingNat : (n - 64#64).toNat = n.toNat - 64 := by
      exact BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using hlong)
    have hremainingLive : SmallRange afterFirst.mem (msg.add 64#64) (n - 64#64).toNat := by
      rw [hremainingNat]
      exact he.smallRange (msg.add 64#64) (n.toNat - 64) hmsgCache (((smallRange_add heinput (k := 64) (count := n.toNat - 64)
        (by omega)).storeAt _ _).storeAt _ _)
    have hremainingRead : readBytes afterFirst.mem (msg.add 64#64) (n - 64#64).toNat = message.drop 64 := by
      have hb : SmallRange es.mem (msg.add 64#64) (n - 64#64).toNat := by
        rw [hremainingNat]
        exact smallRange_add heinput (k := 64) (count := n.toNat - 64) (by omega)
      rw [he.readBytes (msg.add 64#64) (n - 64#64).toNat hmsgCache ((hb.storeAt _ _).storeAt _ _)
        (show (Range.of (ctx.add 128) 512).Disjoint
          (Range.of (msg.add 64#64) (8 * (n - 64#64).toNat)) from Or.inl hne)]
      dsimp only [advanceCount, filled, firstFill]
      rw [readBytes_storeAt_disjoint _ _ _ _ _ (hb.storeAt _ _)
          (show (Range.of (ctx.add 192) 128).Disjoint
            (Range.of (msg.add 64#64) (8 * (n - 64#64).toNat)) from Or.inl hne),
        readBytes_storeAt_disjoint _ _ _ _ _ hb
          (show (Range.of (ctx.add 64#64) 512).Disjoint
            (Range.of (msg.add 64#64) (8 * (n - 64#64).toNat)) from Or.inl hne)]
      rw [← hemessage, readBytes_drop _ _ _ _ hlong, hremainingNat]
    have hout' : OutputResources afterFirst dst copy :=
      ⟨he.smallRange dst 32 houtCache ((heout.output.storeAt _ _).storeAt _ _),
        he.smallRange copy 208 hcopyCache ((heout.copy.storeAt _ _).storeAt _ _)⟩
    have hpreframe : (advanceCount filled ctx 1#64).mem.eraseFrom s.alloc.nextFreeBlock = s.mem :=
      erase_internal_store _ _ _ _ _ (erase_internal_store _ _ _ _ _ heframe hctx) hctx
    have hframe' : CacheFrame cg s.mem (afterFirst.mem.eraseFrom s.alloc.nextFreeBlock) := by
      have hf := he.erase_internal s.alloc.nextFreeBlock hcache hctx
      rw [hpreframe] at hf
      exact hf
    let longEnv := firstEnv (ee[%31 := .value 0#1]) ctx msg n (filled.mem.readAt (ctx.add 192#64) 128)
    have hregs : RemainingRegisters longEnv dst ctx copy (msg.add 64#64) (n - 64#64) := by
      constructor
      · constructor <;> simp [longEnv, firstEnv, ee, entryEnv, ctx, copy, mlir_env, h0]
      all_goals simp [longEnv, firstEnv, ee, entryEnv, ctx, mlir_env]
    have hcount : (firstBlock r a message).length / 128 + (n - 64#64).toNat / 128 < 2 ^ 128 := by
      rw [firstBlock_length r a message (by omega), hremainingNat]
      have := smallRange_length_lt hinput
      omega
    have hdone := remaining_reaches_final_cold cg p g compress hcompress
      longEnv afterFirst dst ctx copy (msg.add 64#64) (n - 64#64)
      (firstBlock r a message) (message.drop 64) s.alloc.nextFreeBlock s.mem
      hregs hwf' hout' hc' hremainingLive hremainingRead hcount hne hcc hoc hctx hcopy hframe' hrFirst hctxK hctxCache hmsgCache houtCache hcopyCache hcache
    apply ColdReachesFinal.prepend (by simpa only [← transcript_split] using hdone)
    rw [hentry, if_neg hshort]
    rw [nonempty_block p g ee es (by simp [ee, entryEnv, mlir_env])
      (by simp [ee, entryEnv, mlir_env])]
    exact first_block p g (ee[%31 := .value 0#1]) es afterFirst ctx msg n
      (by simpa [mlir_env] using heregs.context)
      (by simpa [ee, entryEnv, mlir_env] using h3)
      (by simpa [ee, entryEnv, mlir_env] using h4)
      (by simp [ee, entryEnv, ctx, mlir_env]) (by simp [ee, entryEnv, mlir_env])
      (by simp [ee, entryEnv, mlir_env]) (by simp [ee, entryEnv, mlir_env])
      (by simp [ee, entryEnv, mlir_env]) (by simp [ee, entryEnv, mlir_env])
      hect.live heinput hlong hne hcall


end Agave.Ed25519.Verifier.Execution.Challenge

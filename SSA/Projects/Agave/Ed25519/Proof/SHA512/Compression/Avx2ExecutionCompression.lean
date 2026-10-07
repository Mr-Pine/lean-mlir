import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPrefix
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionFeedForward

/-! Exact imported AVX2 compression from the first schedule-pair header to
the surrounding block-loop continuation. All eighty rounds and the emitted
feed-forward stores are included, with finite execution and memory frames. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem FeedForwardReady.of_groupFrame {E E' : Env program.Γ} {chain : Pointer}
    (h : FeedForwardReady E chain) (hf : GroupFrame E E') : FeedForwardReady E' chain := by
  constructor
  · exact (hf.read (%arg0)).trans h.chainPtr
  · exact (hf.read (%99)).trans h.upper
  · exact (hf.read (%2)).trans h.zero
  · exact (hf.read (%1)).trans h.one
  · exact (hf.read (%42)).trans h.two
  · exact (hf.read (%46)).trans h.three

/-- The exact imported region takes 56 blocks: 39 prefix blocks, 16 tail
blocks, then bb7. Scratch is the only other memory region it may change. -/
theorem compression_from_pairs (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch k chain : Pointer) (block : Bytes) (initial : Spec.State)
    (h : PairReady E scratch k 0 0 (specWindow block 0) initial)
    (hs : PairScratch mem.mem scratch (schedule block) 0 0)
    (hk : PairConstants mem.mem k) (hg : GroupReady E 0) (hl : PairLoopConstants E)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120))
    (hf : FeedForwardReady E chain) (hc : SmallRange mem.mem chain 64)
    (hchain : mem.mem.readAt chain 512 = pack initial)
    (hcs : (Range.of scratch 1024).Disjoint (Range.of chain 512)) :
    ∃ E' scratchState,
      ExecTrace (program g) 56 E 5 mem E' 1
        { scratchState with mem := scratchState.mem.storeAt chain (pack (compressBlock initial block)) } ∧
      ScratchFrame scratch mem scratchState ∧
      ({ scratchState with mem := scratchState.mem.storeAt chain (pack (compressBlock initial block)) } :
        GlobalState).mem.readAt chain 512 = pack (compressBlock initial block) := by
  obtain ⟨Et, mt, hprefix, htail, hsched, hframe, hmem⟩ :=
    prefix_sixtyfour g E mem scratch k block initial h hs hk hg hl hd
  have hc' := hmem.live hc
  have hchain' : mt.mem.readAt chain 512 = pack initial :=
    (hmem.read chain 512 hcs).trans hchain
  obtain ⟨Ef, htrace, hstore, _⟩ :=
    tail_feedForward g Et mt scratch chain initial block hsched htail
      (hf.of_groupFrame hframe) hc' hchain'
  let Eout := (feedForwardEnv Ef initial (roundsFrom initial (schedule block) 0 80))[%86 := .value 1#64]
  refine ⟨Eout, mt, ?_, hmem, ?_⟩
  · exact (hprefix.trans (htrace.execTrace g)).trans (ExecTrace.single hstore)
  · exact MemoryState.readAt_storeAt_self hc'.fits _

/-- Arbitrary continuation behavior is equal after the proven finite compression. -/
theorem compression_from_pairs_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch k chain : Pointer) (block : Bytes) (initial : Spec.State)
    (h : PairReady E scratch k 0 0 (specWindow block 0) initial)
    (hs : PairScratch mem.mem scratch (schedule block) 0 0)
    (hk : PairConstants mem.mem k) (hg : GroupReady E 0) (hl : PairLoopConstants E)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120))
    (hf : FeedForwardReady E chain) (hc : SmallRange mem.mem chain 64)
    (hchain : mem.mem.readAt chain 512 = pack initial)
    (hcs : (Range.of scratch 1024).Disjoint (Range.of chain 512)) :
    ∃ E' scratchState,
      (program g).runFrom E 5 mem = (program g).runFrom E' 1
        { scratchState with mem := scratchState.mem.storeAt chain (pack (compressBlock initial block)) } ∧
      ScratchFrame scratch mem scratchState := by
  obtain ⟨E', m', ht, hm, _⟩ :=
    compression_from_pairs g E mem scratch k chain block initial h hs hk hg hl hd hf hc hchain hcs
  exact ⟨E', m', ht.runFrom, hm⟩

/-- Every observation outside scratch and chaining state is unchanged. -/
theorem compression_frame_read {scratch chain p : Pointer} {mem scratchState : GlobalState}
    {w : Nat} (value : BitVec 512) (hf : ScratchFrame scratch mem scratchState)
    (hs : (Range.of scratch 1024).Disjoint (Range.of p w))
    (hc : (Range.of chain 512).Disjoint (Range.of p w)) :
    (scratchState.mem.storeAt chain value).readAt p w = mem.mem.readAt p w := by
  rw [MemoryState.readAt_storeAt_disjoint hc value]
  exact hf.read p w hs

end Agave.Ed25519.SHA512.Execution.Avx2

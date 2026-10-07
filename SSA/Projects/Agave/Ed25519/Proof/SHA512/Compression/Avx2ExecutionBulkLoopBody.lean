import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairPrefix
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkFinish

/-! The exact dual-message body, from the first vector pair to the outer backedge. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem BulkTailFeedForwardReady.of_bulk_prefix {E E' : Env program.Γ} {s : Spec.State}
    (h : BulkTailFeedForwardReady E s) (hf : RegFrame 448 581 E E') :
    BulkTailFeedForwardReady E' s := by
  rcases h with ⟨ha,hb,hc,hd,he,hf',hg,hh,hz⟩
  constructor
  all_goals first
    | exact (hf.read _).trans ha
    | exact (hf.read _).trans hb
    | exact (hf.read _).trans hc
    | exact (hf.read _).trans hd
    | exact (hf.read _).trans he
    | exact (hf.read _).trans hf'
    | exact (hf.read _).trans hg
    | exact (hf.read _).trans hh
    | exact (hf.read _).trans hz

theorem BulkTailSecondConstants.of_bulk_prefix {E E' : Env program.Γ} {cache : Pointer}
    (h : BulkTailSecondConstants E cache) (hf : RegFrame 448 581 E E') :
    BulkTailSecondConstants E' cache := by
  rcases h with ⟨a,b,c,d,e,f,g,i,j⟩
  constructor
  all_goals first
    | exact (hf.read _).trans a
    | exact (hf.read _).trans b
    | exact (hf.read _).trans c
    | exact (hf.read _).trans d
    | exact (hf.read _).trans e
    | exact (hf.read _).trans f
    | exact (hf.read _).trans g
    | exact (hf.read _).trans i
    | exact (hf.read _).trans j

theorem bulk_pair_body_backedge (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache k : Pointer) (first second : Bytes) (initial : Spec.State)
    (index pairs : BitVec 64)
    (h : BulkPairSpecReady E scratch cache k 0 0 first second initial)
    (hs : PairScratch mem.mem scratch (schedule first) 0 0)
    (hcache : BulkCachePrefix mem.mem cache (schedule second) 16)
    (hk : PairConstants mem.mem k) (hg : BulkGroupReady E 1)
    (hc : BulkPairLoopConstants E cache)
    (hsc : scratch.id ≠ cache.id) (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id)
    (hf : BulkTailFeedForwardReady E initial) (hconst : BulkTailSecondConstants E cache)
    (hcounter : BulkCounterReady E index pairs)
    (hmore : pairs + 18446744073709551615#64 ≠ 0#64) :
    ∃ E' mem', ExecTrace (program g) 137 E 12 mem E' 9 mem' ∧
      BulkOuterReady E' (compressBlock (compressBlock initial first) second)
        (index+2#64) (pairs+18446744073709551615#64) ∧
      RegFrame 350 664 E E' ∧ BulkPairMemFrame scratch cache mem mem' := by
  obtain ⟨E1,m1,ht,htail,hs1,hcache1,hframe,hmem⟩ :=
    bulk_prefix_sixtyfour g E mem scratch cache k first second initial h hs hcache hk hg hc hsc hsk hck
  obtain ⟨E2,ht2,hr2,hframe2⟩ :=
    bulk_finish_backedge g E1 m1 scratch cache initial first second index pairs
      hs1 hcache1 htail (hf.of_bulk_prefix hframe) (hconst.of_bulk_prefix hframe)
      (hcounter.of_frame (hframe.enlarge (by decide) (by decide))) hmore
  exact ⟨E2,m1,ht.trans ht2,hr2,
    (hframe.enlarge (by decide) (by decide)).trans hframe2,hmem⟩

theorem bulk_pair_body_exit (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache k chain : Pointer) (first second : Bytes) (initial : Spec.State)
    (index : BitVec 64)
    (h : BulkPairSpecReady E scratch cache k 0 0 first second initial)
    (hs : PairScratch mem.mem scratch (schedule first) 0 0)
    (hcache : BulkCachePrefix mem.mem cache (schedule second) 16)
    (hk : PairConstants mem.mem k) (hg : BulkGroupReady E 1)
    (hc : BulkPairLoopConstants E cache)
    (hsc : scratch.id ≠ cache.id) (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id)
    (hf : BulkTailFeedForwardReady E initial) (hconst : BulkTailSecondConstants E cache)
    (hcounter : BulkCounterReady E index 1#64) (hp : BulkChainPointers E chain) :
    ∃ E' mem', ExecTrace (program g) 137 E 12 mem E' 17 mem' ∧
      BulkStoreReady E' chain (compressBlock (compressBlock initial first) second) ∧ BulkPairMemFrame scratch cache mem mem' := by
  obtain ⟨E1,m1,ht,htail,hs1,hcache1,hframe,hmem⟩ :=
    bulk_prefix_sixtyfour g E mem scratch cache k first second initial h hs hcache hk hg hc hsc hsk hck
  obtain ⟨E2,ht2,hr2⟩ :=
    bulk_finish_exit g E1 m1 scratch cache chain initial first second index
      hs1 hcache1 htail (hf.of_bulk_prefix hframe) (hconst.of_bulk_prefix hframe)
      (hcounter.of_frame (hframe.enlarge (by decide) (by decide)))
      (hp.of_bulk_frame (hframe.enlarge (by decide) (by decide)))
  exact ⟨E2,m1,ht.trans ht2,hr2,hmem⟩

end Agave.Ed25519.SHA512.Execution.Avx2

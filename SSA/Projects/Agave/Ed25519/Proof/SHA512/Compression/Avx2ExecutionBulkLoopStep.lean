import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialLoadEntry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkLoopBody

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure BulkLoopInvariant (g : Globals) (E : Env program.Γ) (chain scratch cache : Pointer) : Prop where
  constants : BulkInitialEntryReady g E
  pointers : BulkInitialPointers E scratch cache
  chainPointers : BulkChainPointers E chain
  tailConstants : BulkTailSecondConstants E cache
  minusOne : E.read (%80) = .value 18446744073709551615#64

theorem BulkInitialPointers.of_outer_frame {E E' : Env program.Γ} {scratch cache : Pointer}
    (h : BulkInitialPointers E scratch cache) (hf : RegFrame 350 664 E E') :
    BulkInitialPointers E' scratch cache := by
  constructor
  · exact (hf.read (%83)).trans h.scratchPtr
  · exact (hf.read (%82)).trans h.cachePtr
  · exact (hf.read (%321)).trans h.scratch1
  · exact (hf.read (%322)).trans h.cache1
  · exact (hf.read (%323)).trans h.scratch2
  · exact (hf.read (%324)).trans h.cache2
  · exact (hf.read (%325)).trans h.scratch3
  · exact (hf.read (%326)).trans h.cache3
  · exact (hf.read (%327)).trans h.scratch4
  · exact (hf.read (%328)).trans h.cache4
  · exact (hf.read (%329)).trans h.scratch5
  · exact (hf.read (%330)).trans h.cache5
  · exact (hf.read (%331)).trans h.scratch6
  · exact (hf.read (%332)).trans h.cache6
  · exact (hf.read (%333)).trans h.scratch7
  · exact (hf.read (%334)).trans h.cache7

theorem BulkTailSecondConstants.of_outer_frame {E E' : Env program.Γ} {cache : Pointer}
    (h : BulkTailSecondConstants E cache) (hf : RegFrame 350 664 E E') :
    BulkTailSecondConstants E' cache := by
  constructor
  · exact (hf.read (%82)).trans h.cache
  · exact (hf.read (%3)).trans h.eight
  · exact (hf.read (%79)).trans h.limit
  · exact (hf.read (%36)).trans h.rot14
  · exact (hf.read (%37)).trans h.rot18
  · exact (hf.read (%38)).trans h.rot41
  · exact (hf.read (%39)).trans h.rot28
  · exact (hf.read (%40)).trans h.rot34
  · exact (hf.read (%41)).trans h.rot39

theorem BulkLoopInvariant.of_frame {g : Globals} {E E' : Env program.Γ}
    {chain scratch cache : Pointer} (h : BulkLoopInvariant g E chain scratch cache)
    (hf : RegFrame 350 664 E E') : BulkLoopInvariant g E' chain scratch cache :=
  ⟨h.constants.of_frame hf, h.pointers.of_outer_frame hf,
    h.chainPointers.of_bulk_frame hf, h.tailConstants.of_outer_frame hf,
    (hf.read (%80)).trans h.minusOne⟩

theorem BulkOuterReady.feedForward {E : Env program.Γ} {s : Spec.State} {index pairs : BitVec 64}
    (h : BulkOuterReady E s index pairs) (hz : E.read (%2) = .value 0#64) :
    BulkTailFeedForwardReady E s :=
  ⟨h.a,h.b,h.c,h.d,h.e,h.f,h.g,h.h,hz⟩

theorem BulkOuterReady.counters {g : Globals} {E : Env program.Γ} {s : Spec.State}
    {index pairs : BitVec 64} {chain scratch cache : Pointer}
    (h : BulkOuterReady E s index pairs) (hi : BulkLoopInvariant g E chain scratch cache) :
    BulkCounterReady E index pairs :=
  ⟨h.index,h.pairs,hi.constants.v42,hi.minusOne,hi.constants.v2⟩

theorem bulk_loop_pair_backedge (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data scratch cache : Pointer) (n : Nat) (pairs : BitVec 64) (initial : Spec.State)
    (hi : BulkLoopInvariant g E chain scratch cache)
    (ho : BulkOuterReady E initial (BitVec.ofNat 64 n) pairs)
    (hdata : E.read (%arg1) = .value data)
    (hd : SmallRange mem.mem data (128*n+256))
    (hs : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cache 640)
    (hk : PairConstants mem.mem g.address0)
    (hsc : scratch.id ≠ cache.id) (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id)
    (hsk : scratch.id ≠ g.address0.id) (hck : cache.id ≠ g.address0.id)
    (hmore : pairs + 18446744073709551615#64 ≠ 0#64)
    : let p := data.add (BitVec.ofNat 64 (128*n))
      let first := readBytes mem.mem p 128
      let second := readBytes mem.mem (p.add 128#64) 128
      ∃ E' mem', ExecTrace (program g) 139 E 9 mem E' 9 mem' ∧
        BulkOuterReady E' (compressBlock (compressBlock initial first) second)
          (BitVec.ofNat 64 n + 2#64) (pairs+18446744073709551615#64) ∧
        BulkLoopInvariant g E' chain scratch cache ∧ RegFrame 350 664 E E' ∧
        BulkPairMemFrame scratch cache mem mem' := by
  obtain ⟨ht,hready,hs1,hc1,hk1,hg1,hl1,hframe,hmem⟩ :=
    bulk_initial_pair_entry g E mem data scratch cache n pairs initial
      hi.constants hi.pointers ho hdata hd hs hc hk hsc hsd hcd hsk hck
  have hframe' : RegFrame 350 664 E _ := hframe.enlarge (by decide) (by decide)
  have hi1 := hi.of_frame hframe'
  have hfeed := ho.feedForward hi.constants.v2
  have hfeed1 : BulkTailFeedForwardReady
      (bulkInitialPairEnv E data cache n
        (readBytes mem.mem (data.add (BitVec.ofNat 64 (128*n))) 128)
        (readBytes mem.mem ((data.add (BitVec.ofNat 64 (128*n))).add 128#64) 128)) initial := by
    rcases hfeed with ⟨a,b,c,d,e,f,i,j,z⟩
    constructor
    all_goals first
      | exact (hframe.read _).trans a
      | exact (hframe.read _).trans b
      | exact (hframe.read _).trans c
      | exact (hframe.read _).trans d
      | exact (hframe.read _).trans e
      | exact (hframe.read _).trans f
      | exact (hframe.read _).trans i
      | exact (hframe.read _).trans j
      | exact (hframe.read _).trans z
  have hcounter := (ho.counters hi).of_frame (hframe.enlarge (by decide) (by decide))
  obtain ⟨E2,m2,ht2,hr2,hf2,hm2⟩ :=
    bulk_pair_body_backedge g _ _ scratch cache g.address0 _ _ initial (BitVec.ofNat 64 n) pairs
      hready hs1 hc1 hk1 hg1 hl1 hsc hsk hck hfeed1 hi1.tailConstants hcounter hmore
  exact ⟨E2,m2,ht.trans ht2,hr2,hi1.of_frame hf2,hframe'.trans hf2,hmem.trans hm2⟩

theorem bulk_loop_pair_exit (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data scratch cache : Pointer) (n : Nat) (initial : Spec.State)
    (hi : BulkLoopInvariant g E chain scratch cache)
    (ho : BulkOuterReady E initial (BitVec.ofNat 64 n) 1#64)
    (hdata : E.read (%arg1) = .value data)
    (hd : SmallRange mem.mem data (128*n+256))
    (hs : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cache 640)
    (hk : PairConstants mem.mem g.address0)
    (hsc : scratch.id ≠ cache.id) (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id)
    (hsk : scratch.id ≠ g.address0.id) (hck : cache.id ≠ g.address0.id)
    : let p := data.add (BitVec.ofNat 64 (128*n))
      let first := readBytes mem.mem p 128
      let second := readBytes mem.mem (p.add 128#64) 128
      ∃ E' mem', ExecTrace (program g) 139 E 9 mem E' 17 mem' ∧
        BulkStoreReady E' chain (compressBlock (compressBlock initial first) second) ∧
        BulkPairMemFrame scratch cache mem mem' := by
  obtain ⟨ht,hready,hs1,hc1,hk1,hg1,hl1,hframe,hmem⟩ :=
    bulk_initial_pair_entry g E mem data scratch cache n 1#64 initial
      hi.constants hi.pointers ho hdata hd hs hc hk hsc hsd hcd hsk hck
  have hframe' : RegFrame 350 664 E _ := hframe.enlarge (by decide) (by decide)
  have hi1 := hi.of_frame hframe'
  have hfeed := ho.feedForward hi.constants.v2
  have hfeed1 : BulkTailFeedForwardReady
      (bulkInitialPairEnv E data cache n
        (readBytes mem.mem (data.add (BitVec.ofNat 64 (128*n))) 128)
        (readBytes mem.mem ((data.add (BitVec.ofNat 64 (128*n))).add 128#64) 128)) initial := by
    rcases hfeed with ⟨a,b,c,d,e,f,i,j,z⟩
    constructor
    all_goals first
      | exact (hframe.read _).trans a
      | exact (hframe.read _).trans b
      | exact (hframe.read _).trans c
      | exact (hframe.read _).trans d
      | exact (hframe.read _).trans e
      | exact (hframe.read _).trans f
      | exact (hframe.read _).trans i
      | exact (hframe.read _).trans j
      | exact (hframe.read _).trans z
  have hcounter := (ho.counters hi).of_frame (hframe.enlarge (by decide) (by decide))
  obtain ⟨E2,m2,ht2,hr2,hm2⟩ :=
    bulk_pair_body_exit g _ _ scratch cache g.address0 chain _ _ initial (BitVec.ofNat 64 n)
      hready hs1 hc1 hk1 hg1 hl1 hsc hsk hck hfeed1 hi1.tailConstants hcounter hi1.chainPointers
  exact ⟨E2,m2,ht.trans ht2,hr2,hmem.trans hm2⟩

end Agave.Ed25519.SHA512.Execution.Avx2

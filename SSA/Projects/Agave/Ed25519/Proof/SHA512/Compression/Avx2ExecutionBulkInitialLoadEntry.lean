import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialLoadReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTrace

/-! Initial dual-block input decoding supplies the complete bb12 invariant. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem bulk_initial_pair_entry (g : Globals) (E : Env program.Γ) (origin mem : GlobalState)
    (data scratch cache : Pointer) (n : Nat) (pairs : BitVec 64) (s : Spec.State)
    (he : EntryReady g E origin) (hp : BulkInitialPointers E scratch cache)
    (ho : BulkOuterReady E s (BitVec.ofNat 64 n) pairs)
    (hdata : E.read (%arg1) = .value data)
    (hd : SmallRange mem.mem data (128*n+256))
    (hs : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cache 640)
    (hk : PairConstants mem.mem g.address0)
    (hsc : scratch.id ≠ cache.id) (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id)
    (hsk : scratch.id ≠ g.address0.id) (hck : cache.id ≠ g.address0.id) :
    let p := data.add (BitVec.ofNat 64 (128*n))
    let first := readBytes mem.mem p 128
    let second := readBytes mem.mem (p.add 128#64) 128
    let E' := bulkInitialPairEnv E data cache n first second
    let mem' := bulkInitialStores mem scratch cache first second 8
    ExecTrace (program g) 2 E 9 mem E' 12 mem' ∧
      BulkPairSpecReady E' scratch cache g.address0 0 0 first second s ∧
      PairScratch mem'.mem scratch (schedule first) 0 0 ∧
      BulkCachePrefix mem'.mem cache (schedule second) 16 ∧
      PairConstants mem'.mem g.address0 ∧
      BulkGroupReady E' 1 ∧ BulkPairLoopConstants E' cache ∧
      RegFrame 360 487 E E' ∧ BulkPairMemFrame scratch cache mem mem' := by
  let p := data.add (BitVec.ofNat 64 (128*n))
  let first := readBytes mem.mem p 128
  let second := readBytes mem.mem (p.add 128#64) 128
  have hload := BulkInitialLoadReady.of_entry g E origin data scratch cache n he hp hdata ho.index
  have hframe := bulkInitialStores_frame mem scratch cache first second 8
  refine ⟨?_, bulkInitialPairEnv_ready g E origin data scratch cache n pairs first second s he hp ho,
    bulkInitialStores_scratch mem scratch cache first second hs hsc,
    bulkInitialStores_cache mem scratch cache first second 8 (by decide) hc hsc,
    bulkInitialStores_constants mem scratch cache g.address0 first second 8 hk hsk hck,
    bulkInitialPairEnv_group g E origin data cache n first second he,
    bulkInitialPairEnv_loopConstants g E origin data scratch cache n first second he hp,
    bulkInitialPairEnv_frame E data cache n first second, hframe⟩
  exact ExecTrace.step (bulk_initial_load_run E mem data scratch cache n hload hd hs hc hsd hcd)
    (ExecTrace.single (bulk_initial_pair_setup_run g E origin
      (bulkInitialStores mem scratch cache first second 8) data scratch cache n first second
      he hp (hframe.live hc)))

/-- The sibling bb8 setup composes directly with the exact initializer. -/
theorem bulk_initial_setup_pair_entry (g : Globals) (E : Env program.Γ) (origin mem : GlobalState)
    (chain data scratch cache : Pointer) (n : Nat) (pairs : BitVec 64) (s : Spec.State)
    (he : EntryReady g E origin) (h : BulkInitialReady E chain scratch cache)
    (hn : E.read (%86) = .value (BitVec.ofNat 64 n)) (hpair : E.read (%90) = .value pairs)
    (hdata : E.read (%arg1) = .value data)
    (hchain : SmallRange mem.mem chain 64) (hr : InitialChainReads mem.mem chain s)
    (hd : SmallRange mem.mem data (128*n+256))
    (hs : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cache 640)
    (hk : PairConstants mem.mem g.address0)
    (hsc : scratch.id ≠ cache.id) (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id)
    (hsk : scratch.id ≠ g.address0.id) (hck : cache.id ≠ g.address0.id) :
    let p := data.add (BitVec.ofNat 64 (128*n))
    let first := readBytes mem.mem p 128
    let second := readBytes mem.mem (p.add 128#64) 128
    ∃ E' mem', ExecTrace (program g) 3 E 8 mem E' 12 mem' ∧
      BulkPairSpecReady E' scratch cache g.address0 0 0 first second s ∧
      PairScratch mem'.mem scratch (schedule first) 0 0 ∧
      BulkCachePrefix mem'.mem cache (schedule second) 16 ∧
      PairConstants mem'.mem g.address0 ∧
      BulkGroupReady E' 1 ∧ BulkPairLoopConstants E' cache ∧
      RegFrame 321 487 E E' ∧ BulkPairMemFrame scratch cache mem mem' := by
  let E1 := bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s)
  have hf : RegFrame 321 487 E E1 :=
    (bulk_initial_setup_frame E chain scratch cache s).enlarge (by decide) (by decide)
  have he1 := he.of_bulk_initial_frame hf
  have hp1 := (bulk_initial_setup_pointers E chain scratch cache s h).2
  have ho1 := bulk_initial_setup_ready E chain scratch cache s (BitVec.ofNat 64 n) pairs hn hpair
  have hdata1 : E1.read (%arg1) = .value data := (hf.read (%arg1)).trans hdata
  obtain ⟨ht, hready, hs', hc', hk', hg', hl', he', hm'⟩ :=
    bulk_initial_pair_entry g E1 origin mem data scratch cache n pairs s he1 hp1 ho1
      hdata1 hd hs hc hk hsc hsd hcd hsk hck
  refine ⟨_, _, ExecTrace.step
    (bulk_initial_setup_run E mem chain scratch cache s h hchain hs hc hr) ht,
    hready, hs', hc', hk', hg', hl', hf.trans (he'.enlarge (by decide) (by decide)), hm'⟩

end Agave.Ed25519.SHA512.Execution.Avx2

import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSeed
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkLoopInitial
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkLoopReturn

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

theorem bulk_zeroFill_frame (mem : GlobalState) (scratch cache : Pointer) :
    BulkPairMemFrame scratch cache mem (returnState mem cache) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro p w hs hc
    exact bulk_read_store_ne mem.mem (cache.add 128#64) p _ w (by simpa using hc)
  · intro p n h
    exact h.storeAt _ _
  · intro mark hs hc
    exact returnState_erase mem cache mark hc

/-- The real outer test, cache zero fill, and setup precede all remaining pairs. -/
theorem bulk_from_test_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data scratch cache : Pointer) (index k : Nat)
    (hseed : BulkSeed g E chain scratch cache)
    (hcount : E.read (%arg2) = .value (BitVec.ofNat 64 (index+2*(k+1))))
    (hindex : E.read (%86) = .value (BitVec.ofNat 64 index))
    (hdata : E.read (%arg1) = .value data)
    (hb : index+2*(k+1) < 2^56)
    (hd : SmallRange mem.mem data (128*(index+2*(k+1))))
    (hchain : SmallRange mem.mem chain 64) (hs : SmallRange mem.mem scratch 128)
    (hc : SmallRange mem.mem cache 640) (hk : PairConstants mem.mem g.address0)
    (hsc : scratch.id ≠ cache.id) (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id)
    (hsk : scratch.id ≠ g.address0.id) (hck : cache.id ≠ g.address0.id)
    (hcachechain : cache.id ≠ chain.id) :
    ∃ mem', (program g).evalFrom (139*(k+1)+4) E 1 mem =
      .value (some .nil, {mem' with mem := (mem'.mem.storeAt chain
        (Spec.run (mem.mem.readAt chain 512)
          (readBytes mem.mem (data.add (BitVec.ofNat 64 (128*index))) (256*(k+1)))))}) ∧
      BulkPairMemFrame scratch cache mem mem' := by
  let E1 := bulkTestEnv E cache (k+1)
  let m1 := returnState mem cache
  have htest := bulk_test_pairs E mem cache index (k+1) (by omega) hb
    (hseed.testReady _ _ hcount hindex) hc
  have htestframe := bulkTestEnv_frame E cache (k+1)
  have hseed1 : BulkSeed g E1 chain scratch cache :=
    hseed.of_frame (htestframe.enlarge (by decide) (by decide))
  have hm := bulk_zeroFill_frame mem scratch cache
  have hread : m1.mem.readAt chain 512 = mem.mem.readAt chain 512 :=
    bulk_read_store_ne mem.mem (cache.add 128#64) chain _ 512 (by simpa using hcachechain)
  have hreads := initialChainReads_unpack m1.mem chain (hm.live hchain)
  rw [hread] at hreads
  obtain ⟨ht8,hi8,ho8,hframe8⟩ := bulk_initial_setup_loop_entry g E1 m1 chain scratch cache
    (unpack (mem.mem.readAt chain 512)) (BitVec.ofNat 64 index) (BitVec.ofNat 64 (k+1))
    hseed1.constants hseed1.initial hseed1.tail hseed1.minusOne
    ((htestframe.read (%86)).trans hindex) (by simp [E1,bulkTestEnv,mlir_env])
    (hm.live hchain) (hm.live hs) (hm.live hc) hreads
  obtain ⟨m2,heval,hm2⟩ := bulk_loop_evalFrom g chain data scratch cache hsc hsd hcd hsk hck k
    _ m1 index (unpack (mem.mem.readAt chain 512)) hi8 ho8
    ((hframe8.read (%arg1)).trans ((htestframe.read (%arg1)).trans hdata))
    hb (hm.live hd) (hm.live hs) (hm.live hc) (hm.constants hk hsk hck) (hm.live hchain)
  refine ⟨m2,?_,hm.trans hm2⟩
  have ht := (ExecTrace.single (f := program g) (i := 1) (E := E) (mem := mem) htest).trans ht8
  rw [show 139*(k+1)+4 = 2+(139*(k+1)+2) by omega, ht.evalFrom]
  have hrb : readBytes m1.mem (data.add (BitVec.ofNat 64 (128*index))) (256*(k+1)) =
      readBytes mem.mem (data.add (BitVec.ofNat 64 (128*index))) (256*(k+1)) :=
    hm.readBytes _ _ (by simpa using hsd) (by simpa using hcd)
  simpa only [pack_unpack, hrb] using heval

end Agave.Ed25519.SHA512.Execution.Avx2

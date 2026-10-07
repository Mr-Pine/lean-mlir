import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkCallMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkEven

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem bulk_odd_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (k : Nat) (hwf : mem.WF)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data (128*(1+2*(k+1))))
    (hk : PairConstants mem.mem g.address0) (hchainK : chain.id ≠ g.address0.id)
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8*(128*(1+2*(k+1))))))
    (hb : 1+2*(k+1)<2^56)
    (hp : E.read (%arg0) = .value chain) (hq : E.read (%arg1) = .value data)
    (hn : E.read (%arg2) = .value (BitVec.ofNat 64 (1+2*(k+1)))) :
    ∃ mout, (program g).evalFrom (139*(k+1)+63) E 0 mem = .value (some .nil,mout) ∧
      mout.mem.eraseFrom mem.alloc.nextFreeBlock = mem.mem.storeAt chain
        (Spec.run (mem.mem.readAt chain 512) (readBytes mem.mem data (128*(1+2*(k+1))))) ∧
      mout.alloc.nextFreeBlock = mem.alloc.nextFreeBlock+3 := by
  let count := BitVec.ofNat 64 (1+2*(k+1))
  let scratch := ((mem.alloca 128).alloca 640).allocaPtr
  let cache := (mem.alloca 128).allocaPtr
  let first := compressBlock (unpack (mem.mem.readAt chain 512)) (readBytes mem.mem data 128)
  have hd0 : SmallRange mem.mem data 128 := live_prefix hd (by omega)
  have hparity : bulkParity count = 1#64 := by
    rw [bulkParity_eq]
    have hbound : 1+2*(k+1)<2^64 := by omega
    simp only [count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hbound]
    congr 1
    omega
  obtain ⟨E1,mt,ht,hframe,herase,hregs,hconsumed⟩ :=
    bulk_odd_entry_compress g E mem chain data hwf hc hd0 hk hp hq count hn hparity
  let m1 : GlobalState := {mt with mem := mt.mem.storeAt chain (pack first)}
  have hseed : BulkSeed g E1 chain scratch cache := (entryEnv_seed g E mem chain hp).of_frame hregs
  have heframe := entry_frame g E mem
  obtain ⟨h0data,hcdata,hsdata⟩ := entry_slots_ne_old hwf hd
  obtain ⟨h0k,hck,hsk⟩ := entry_slots_ne_old hwf hk.live
  have hcc := (entry_slots_ne_old hwf hc).2.1
  have hsc : scratch.id ≠ cache.id := (entry_slots_distinct mem).2.2.symm
  have hchain : SmallRange mt.mem chain 64 := hframe.live (entryState_live hwf hc)
  have hchainread : m1.mem.readAt chain 512 = pack first :=
    MemoryState.readAt_storeAt_self hchain.fits _
  have hd1 : SmallRange m1.mem data (128*(1+2*(k+1))) :=
    (hframe.live (entryState_live hwf hd)).storeAt _ _
  have hconstants : PairConstants m1.mem g.address0 :=
    ((hk.entryState hwf).scratchFrame hframe h0k).store_ne _ hchainK
  obtain ⟨m2,heval,hm⟩ := bulk_from_test_evalFrom g E1 m1 chain data scratch cache 1 k
    hseed ((hregs.read (%arg2)).trans ((heframe.read (%arg2)).trans hn)) hconsumed
    ((hregs.read (%arg1)).trans ((heframe.read (%arg1)).trans hq)) hb hd1 (hchain.storeAt _ _)
    ((hframe.live (entry_buffer_live mem hwf)).storeAt _ _)
    ((hframe.live (entry_cache_live mem hwf)).storeAt _ _) hconstants
    hsc hsdata hcdata hsk hck hcc
  have hsuffix : SmallRange mem.mem (data.add 128#64) (256*(k+1)) :=
    subrange hd (offset := 128) (by omega)
  have hdisSuffix : (Range.of chain 512).Disjoint (Range.of (data.add 128#64) (8*(256*(k+1)))) :=
    bulk_range_disjoint_add_right hd (off := 128) (by omega) hdis
  have hreadSuffix : readBytes m1.mem (data.add 128#64) (256*(k+1)) =
      readBytes mem.mem (data.add 128#64) (256*(k+1)) := by
    rw [bulk_readBytes_store_disjoint mt.mem chain (data.add 128#64) (pack first) _
      (hframe.live (entryState_live hwf hsuffix)) hdisSuffix,
      hframe.readBytes_ne _ _ (by simpa using h0data),entryState_readBytes hwf hsuffix]
  have hspec : Spec.run (pack first) (readBytes mem.mem (data.add 128#64) (256*(k+1))) =
      Spec.run (mem.mem.readAt chain 512) (readBytes mem.mem data (128*(1+2*(k+1)))) := by
    have hh := run_readBytes_succ (unpack (mem.mem.readAt chain 512)) mem.mem data (2*(k+1))
    rw [pack_unpack] at hh
    rw [show 128*(2*(k+1)+1) = 128*(1+2*(k+1)) by omega,
      show 128*(2*(k+1)) = 256*(k+1) by omega] at hh
    exact hh.symm
  change (program g).evalFrom (139*(k+1)+4) E1 1 m1 =
    .value (some .nil, {m2 with mem := (m2.mem.storeAt chain
      (Spec.run (m1.mem.readAt chain 512) (readBytes m1.mem (data.add 128#64) (256*(k+1)))))}) at heval
  rw [hchainread,hreadSuffix,hspec] at heval
  let result := Spec.run (mem.mem.readAt chain 512) (readBytes mem.mem data (128*(1+2*(k+1))))
  refine ⟨{m2 with mem := m2.mem.storeAt chain result},?_,?_,?_⟩
  · rw [show 139*(k+1)+63 = 59+(139*(k+1)+4) by omega,ht.evalFrom]
    exact heval
  · rw [MemoryState.eraseFrom_storeAt,hm.erase mem.alloc.nextFreeBlock
      (by simp only [scratch,GlobalState.allocaPtr,GlobalState.alloca]; omega)
      (by simp [cache,GlobalState.allocaPtr,GlobalState.alloca])]
    change ((mt.mem.storeAt chain (pack first)).eraseFrom mem.alloc.nextFreeBlock).storeAt chain result = _
    rw [MemoryState.eraseFrom_storeAt,herase,bulk_store_overwrite]
  · change m2.alloc.nextFreeBlock = _
    rw [hm.alloc]
    change mt.alloc.nextFreeBlock = _
    rw [hframe.alloc,entryState_counter]

theorem bulk_odd_call (g : Globals) (mem : GlobalState) (chain data : Pointer)
    (k : Nat) (hwf : mem.WF) (hc : SmallRange mem.mem chain 64)
    (hd : SmallRange mem.mem data (128*(1+2*(k+1)))) (hk : PairConstants mem.mem g.address0)
    (hchainK : chain.id ≠ g.address0.id)
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8*(128*(1+2*(k+1))))))
    (hb : 1+2*(k+1)<2^56) :
    (program g).call (.cons (.value chain) (.cons (.value data)
      (.cons (.value (BitVec.ofNat 64 (1+2*(k+1)))) .nil))) mem =
      .value (.nil, {
        alloc := ⟨mem.alloc.nextFreeBlock+3⟩,
        mem := mem.mem.storeAt chain (Spec.run (mem.mem.readAt chain 512)
          (readBytes mem.mem data (128*(1+2*(k+1)))))}) := by
  let args : Vals program.Γ.args := .cons (.value chain) (.cons (.value data)
    (.cons (.value (BitVec.ofNat 64 (1+2*(k+1)))) .nil))
  obtain ⟨mout,heval,herase,halloc⟩ := bulk_odd_evalFrom g (Env.init args.get) mem chain data k
    hwf hc hd hk hchainK hdis hb rfl rfl rfl
  have hrun := bulk_run_of_eval g args mem _ mout heval
  have hcall := Func.call_of_run hrun
  rw [herase] at hcall
  have ha : mout.alloc = ⟨mem.alloc.nextFreeBlock+3⟩ := by
    cases h : mout.alloc
    simp only [h] at halloc
    exact congrArg AllocState.mk halloc
  simpa only [args,ha] using hcall

end Agave.Ed25519.SHA512.Execution.Avx2

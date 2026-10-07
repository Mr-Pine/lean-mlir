import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkFuel
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkStart
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionEntryFacts

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

theorem bulk_even_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (k : Nat) (hwf : mem.WF)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data (256*(k+1)))
    (hk : PairConstants mem.mem g.address0) (hb : 2*(k+1)<2^56)
    (hp : E.read (%arg0) = .value chain) (hq : E.read (%arg1) = .value data)
    (hn : E.read (%arg2) = .value (BitVec.ofNat 64 (2*(k+1)))) :
    ∃ mout, (program g).evalFrom (139*(k+1)+5) E 0 mem = .value (some .nil,mout) ∧
      mout.mem.eraseFrom mem.alloc.nextFreeBlock = mem.mem.storeAt chain
        (Spec.run (mem.mem.readAt chain 512) (readBytes mem.mem data (256*(k+1)))) ∧
      mout.alloc.nextFreeBlock = mem.alloc.nextFreeBlock+3 := by
  let count := BitVec.ofNat 64 (2*(k+1))
  let E0 := bulkEntryEnv g E mem count
  let E1 := E0[%86 := .value 0#64]
  let scratch := ((mem.alloca 128).alloca 640).allocaPtr
  let cache := (mem.alloca 128).allocaPtr
  have hparity : bulkParity count = 0#64 := by
    rw [bulkParity_eq]
    have hbound : 2*(k+1)<2^64 := by omega
    simp only [count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hbound]
    simp
  have hf : RegFrame 86 320 E0 E1 :=
    (RegFrame.refl _ _ E0).write _ _ (by decide) (by decide)
  have hseed : BulkSeed g E1 chain scratch cache :=
    (bulkEntryEnv_seed g E mem count chain hp).of_frame hf
  have heframe := bulkEntryEnv_frame g E mem count
  have hcount : E1.read (%arg2) = .value (BitVec.ofNat 64 (0+2*(k+1))) :=
    by simpa only [Nat.zero_add] using (hf.read (%arg2)).trans ((heframe.read (%arg2)).trans hn)
  have hd' : SmallRange (entryState mem).mem data (128*(0+2*(k+1))) := by
    convert entryState_live hwf hd using 1 <;> omega
  obtain ⟨_,hcdata,hsdata⟩ := entry_slots_ne_old hwf hd
  obtain ⟨_,hck,hsk⟩ := entry_slots_ne_old hwf hk.live
  have hcc := (entry_slots_ne_old hwf hc).2.1
  have hsc : scratch.id ≠ cache.id := (entry_slots_distinct mem).2.2.symm
  obtain ⟨m2,heval,hm⟩ := bulk_from_test_evalFrom g E1 (entryState mem) chain data scratch cache 0 k
    hseed hcount (by simp [E1,mlir_env])
    ((hf.read (%arg1)).trans ((heframe.read (%arg1)).trans hq)) (by simpa using hb)
    hd' (entryState_live hwf hc) (entry_buffer_live mem hwf) (entry_cache_live mem hwf)
    (hk.entryState hwf) hsc hsdata hcdata hsk hck hcc
  rw [entryState_read hwf hc 512] at heval
  simp only [Nat.mul_zero,Pointer.add_zero,entryState_readBytes hwf hd] at heval
  refine ⟨{m2 with mem := (m2.mem.storeAt chain
    (Spec.run (mem.mem.readAt chain 512) (readBytes mem.mem data (256*(k+1)))))},?_,?_,?_⟩
  · rw [show 139*(k+1)+5 = (139*(k+1)+4)+1 by omega, Func.evalFrom]
    change ((program.bb0 g).run program.blockParams E mem >>= _) = _
    rw [bulk_entry_even g E mem count hn hparity]
    exact heval
  · rw [MemoryState.eraseFrom_storeAt,hm.erase mem.alloc.nextFreeBlock
      (by simp only [scratch,GlobalState.allocaPtr,GlobalState.alloca]; omega)
      (by simp [cache,GlobalState.allocaPtr,GlobalState.alloca]),entryState_frame mem hwf]
  · change m2.alloc.nextFreeBlock = _
    rw [hm.alloc,entryState_counter]


theorem bulk_even_call (g : Globals) (mem : GlobalState) (chain data : Pointer)
    (k : Nat) (hwf : mem.WF) (hc : SmallRange mem.mem chain 64)
    (hd : SmallRange mem.mem data (256*(k+1))) (hk : PairConstants mem.mem g.address0)
    (hb : 2*(k+1)<2^56) :
    (program g).call (.cons (.value chain) (.cons (.value data)
      (.cons (.value (BitVec.ofNat 64 (2*(k+1)))) .nil))) mem =
      .value (.nil, {
        alloc := ⟨mem.alloc.nextFreeBlock+3⟩,
        mem := mem.mem.storeAt chain (Spec.run (mem.mem.readAt chain 512)
          (readBytes mem.mem data (256*(k+1))))}) := by
  let args : Vals program.Γ.args := .cons (.value chain) (.cons (.value data)
    (.cons (.value (BitVec.ofNat 64 (2*(k+1)))) .nil))
  obtain ⟨mout,heval,herase,halloc⟩ := bulk_even_evalFrom g (Env.init args.get) mem chain data k
    hwf hc hd hk hb rfl rfl rfl
  have hrun : (program g).run args mem = .value (.nil,mout) :=
    Func.run_of_successful_evalFrom (program g) args mem _ .nil mout heval
  have hcall := Func.call_of_run hrun
  rw [herase] at hcall
  have ha : mout.alloc = ⟨mem.alloc.nextFreeBlock+3⟩ := by
    cases h : mout.alloc
    simp only [h] at halloc
    exact congrArg AllocState.mk halloc
  simpa only [args,ha] using hcall

theorem bulk_run_of_eval (g : Globals) (args : Vals program.Γ.args) (mem : GlobalState)
    (fuel : Nat) (mout : GlobalState)
    (h : (program g).evalFrom fuel (Env.init args.get) 0 mem = .value (some .nil,mout)) :
    (program g).run args mem = .value (.nil,mout) :=
  Func.run_of_successful_evalFrom (program g) args mem fuel .nil mout h

end Agave.Ed25519.SHA512.Execution.Avx2

import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreOuter

/-! Actual imported scalar core call correctness, from caller memory readiness.
The private schedule allocation is created by the source entry and removed by
the source call semantics. No execution equality is assumed. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-- The actual core call returns the SHA-512 chaining result and preserves every
other caller-visible live-memory byte, allocation counter, and global symbol. -/
theorem executes (before : GlobalState) (kp chain data : Pointer) (count : Word)
    (h : Ready before kp chain data count) : Executes before chain data count := by
  let stack : Pointer := ⟨⟨before.alloc.nextFreeBlock⟩, 0⟩
  let allocated := before.afterAlloca 1024
  let initial := chainState before.mem chain
  let n := count.toNat - 1
  have hn : n + 1 = count.toNat := by have hp := h.positive; dsimp [n]; omega
  have hcount : BitVec.ofNat 64 (n+1) = count := by rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hchain : SmallRange allocated.mem chain 64 := h.chainRange.afterAlloca h.wf 1024
  have hdata : SmallRange allocated.mem data (128*(n+1)) := by
    rw [hn]
    exact h.dataRange.afterAlloca h.wf 1024
  have hk : SmallRange allocated.mem kp 640 := h.constantsRange.afterAlloca h.wf 1024
  have hstack : SmallRange allocated.mem stack 128 := by
    refine ⟨{length := 128, bytes := 0#1024}, live?_afterAlloca_self before 1024, by decide, ?_⟩
    change (0 : Nat) + 128 ≤ 128
    decide
  have hkp_lt := lt_nextFreeBlock_of_fits h.wf h.constantsRange.fits
  have hdata_lt := lt_nextFreeBlock_of_fits h.wf h.dataRange.fits
  have hsk : stack.id ≠ kp.id := by
    intro he
    have := congrArg BlockId.id he
    dsimp [stack] at this
    omega
  have hsd : stack.id ≠ data.id := by
    intro he
    have := congrArg BlockId.id he
    dsimp [stack] at this
    omega
  have htable : ∀ j, j < 80 → readBits allocated.mem
      (kp.withOffset (BitVec.ofNat 64 (8*j))) 64 = constants.toList.getD j 0 := by
    intro j hj
    apply constants_word _ _ hk _ j hj
    rw [readBits_afterAlloca h.constantsRange.fits h.wf]
    exact h.constantsValue
  obtain ⟨middle, hrun, _, _, _, hframe⟩ := outer_blocks n kp chain stack data data count
    initial initial allocated (h.wf.afterAlloca 1024) hchain hstack hdata hk
    hsk hsd h.constantsSeparate (by rw [hn]; exact h.inputDisjoint) htable
  have hbody : StateT.run (core.denote
      (Ctxt.Valuation.ofHVector [.value count, .value data, .value chain]ₕ)) before =
      .value (.nil, middle) := by
    simp only [Cfg.denote]
    change StateT.run (core.cfgEntry.denote
      (Ctxt.Valuation.ofHVector [.value count, .value data, .value chain]ₕ) >>= _) before = _
    rw [entry_cont before kp chain data count h.wf h.chainRange h.constantsPtr]
    simpa only [hcount, core, stack, initial, allocated] using hrun
  have hbytes : readBytes allocated.mem data (128*(n+1)) =
      readBytes before.mem data (128*count.toNat) := by
    rw [hn]
    unfold readBytes
    have hf : Fits before.mem data ((128*count.toNat)*8) := by
      simpa only [Nat.mul_comm] using h.dataRange.fits
    rw [readBits_afterAlloca hf h.wf]
  have hout : Spec.run (pack initial) (readBytes allocated.mem data (128*(n+1))) =
      result before chain data count := by
    rw [hbytes, pack_chainState before.mem chain h.chainRange]
    rfl
  have hcallerframe : ∀ b : BlockId, b ≠ ⟨before.alloc.nextFreeBlock⟩ →
      middle.mem.live? b = (before.mem.splice chain (result before chain data count)).live? b := by
    intro b hb
    rw [hframe b hb, hout]
    apply live_splice_congr
    have hne : (⟨before.alloc.nextFreeBlock⟩ : BlockId) ≠ b := Ne.symm hb
    simp [allocated, GlobalState.afterAlloca, MemoryState.live?, MemoryState.getElem?_eq,
      Std.HashMap.getElem?_insert, hne]
  exact ⟨before.popFrame middle.mem, run_runFunction hbody, popFrame_wf before middle.mem,
    rfl, rfl, scratch_popFrame_live before middle chain _ h.wf hcallerframe⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core

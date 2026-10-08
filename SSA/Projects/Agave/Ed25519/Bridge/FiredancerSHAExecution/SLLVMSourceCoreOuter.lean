import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreLoops
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFeedforwardRun
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreBlockBytes
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFrames

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] feedforwardMemory

/-- All eighty source rounds and the source addback/branch execute for one
current input block, even when further blocks remain. -/
theorem outer_step (kp chain stack originalData data : Pointer)
    (originalCount count : Word) (original initial : State) (before : GlobalState)
    (hc : SmallRange before.mem chain 64) (hs : SmallRange before.mem stack 128)
    (hd : SmallRange before.mem data 128) (hk : SmallRange before.mem kp 640)
    (hsk : stack.id ≠ kp.id) (hsd : stack.id ≠ data.id)
    (hn : 0 < count.toNat) (hb : count.toNat < 2^63)
    (htable : ∀ j, j < 80 → readBits before.mem (kp.withOffset (BitVec.ofNat 64 (8*j))) 64 = constants.toList.getD j 0) :
    ∃ middle,
      RingWrites stack before middle ∧
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (outerTarget initial data count)) before =
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (if count=1#64 then doneTarget else outerTarget
          (compressBlock initial (readBytes before.mem data 128)) (data.withOffset 128#64) (count-1#64)))
        {middle with mem := feedforwardMemory middle.mem chain (compressBlock initial (readBytes before.mem data 128))} := by
  have hfirst : FirstMemory before.mem stack data kp (readBytes before.mem data 128) 0 :=
    ⟨hs, hd, hk, hsk, hsd, initialRingMemory_zero _ _ _, htable, rfl⟩
  obtain ⟨middle, hrounds, hw⟩ := eighty_rounds kp chain stack originalData data originalCount count
    original initial _ before hfirst
  refine ⟨middle, hw, ?_⟩
  rw [hrounds, feedforward_run kp chain stack originalData data originalCount count original initial
    (roundsFrom initial (schedule (readBytes before.mem data 128)) 0 80) middle
    (hw.smallRange chain 64 hc) hn hb]
  rfl

private theorem readBytes_length (m : MemoryState) (p : Pointer) (n : Nat) :
    (readBytes m p n).length = n := by simp [readBytes, Firedancer.Common.bytesOf]

theorem input_tail_disjoint {m : MemoryState} {chain data : Pointer} {n : Nat}
    (hd : SmallRange m data (128*(n+1))) (h : Disjoint chain 64 data (128*(n+1))) :
    Disjoint chain 64 (data.withOffset 128#64) (128*n) := by
  have hoff := feedforward_data_no_wrap (hd.mono (by omega : 128 ≤ 128*(n+1)))
  simp only [Disjoint, Pointer.withOffset] at h ⊢
  change chain.id ≠ data.id ∨ chain.offset.toNat+64 ≤ (data.offset+128#64).toNat ∨
    (data.offset+128#64).toNat+128*n ≤ chain.offset.toNat
  change (data.offset+128#64).toNat=data.offset.toNat+128 at hoff
  rw [hoff]
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem run_readBytes_cons (m : MemoryState) (data : Pointer) (s : State) (n : Nat)
    (hd : SmallRange m data (128*(n+1))) :
    Spec.run (pack s) (readBytes m data (128*(n+1))) =
      Spec.run (pack (compressBlock s (readBytes m data 128)))
        (readBytes m (data.withOffset 128#64) (128*n)) := by
  rw [readBytes_blocks_succ m data n hd, Spec.run_append _ _ _ (by simp [readBytes_length]),
    Spec.run_one_block _ _ (readBytes_length _ _ _), compressBlockBytes, unpack_pack]

/-- Every positive number of actual source outer-loop iterations terminates;
all caller blocks have exactly one chaining-result overwrite. -/
theorem outer_blocks (n : Nat) :
    ∀ (kp chain stack originalData data : Pointer) (originalCount : Word)
      (original initial : State) (before : GlobalState),
    before.WF → SmallRange before.mem chain 64 → SmallRange before.mem stack 128 →
    SmallRange before.mem data (128*(n+1)) → SmallRange before.mem kp 640 →
    stack.id ≠ kp.id → stack.id ≠ data.id → chain.id ≠ kp.id →
    Disjoint chain 64 data (128*(n+1)) →
    (∀ j, j < 80 → readBits before.mem (kp.withOffset (BitVec.ofNat 64 (8*j))) 64 = constants.toList.getD j 0) →
    ∃ after,
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (outerTarget initial data (BitVec.ofNat 64 (n+1)))) before = .value (.nil, after) ∧
      after.WF ∧ after.alloc=before.alloc ∧ after.globals=before.globals ∧
      ∀ b, b ≠ stack.id → after.mem.live? b =
        (before.mem.splice chain (Spec.run (pack initial) (readBytes before.mem data (128*(n+1))))).live? b := by
  induction n with
  | zero =>
    intro kp chain stack originalData data originalCount original initial before hwf hc hs hd hk hsk hsd hck hdis htable
    obtain ⟨middle, hw, hstep⟩ := outer_step kp chain stack originalData data originalCount 1#64
      original initial before hc hs hd hk hsk hsd (by decide) (by decide) htable
    let result := compressBlock initial (readBytes before.mem data 128)
    refine ⟨{middle with mem := feedforwardMemory middle.mem chain result}, ?_,
      feedforwardState_wf _ _ _ (hw.wf hwf), hw.alloc, hw.globals, ?_⟩
    · rw [hstep]
      simpa only [ite_true] using done_run (ambient kp chain stack originalData originalCount original)
        {middle with mem := feedforwardMemory middle.mem chain result}
    · intro b hb
      rw [feedforwardMemory_live _ _ (hw.smallRange chain 64 hc)]
      rw [Spec.run_one_block _ _ (readBytes_length _ _ _), compressBlockBytes, unpack_pack]
      exact live_splice_congr chain _ b (hw.live b (Ne.symm hb))
  | succ n ih =>
    intro kp chain stack originalData data originalCount original initial before hwf hc hs hd hk hsk hsd hck hdis htable
    have hbound : n+1+1 < 2^63 := by have := hd.offset_lt; omega
    have h64 : n+1+1 < 2^64 := by omega
    have hcount : (BitVec.ofNat 64 (n+1+1)).toNat=n+1+1 := by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    obtain ⟨middle, hw, hstep⟩ := outer_step kp chain stack originalData data originalCount (BitVec.ofNat 64 (n+1+1))
      original initial before hc hs (hd.mono (by omega)) hk hsk hsd
      (by rw [hcount]; omega) (by rw [hcount]; exact hbound) htable
    let result := compressBlock initial (readBytes before.mem data 128)
    let next : GlobalState := {middle with mem := feedforwardMemory middle.mem chain result}
    have hnext (b : BlockId) : next.mem.live? b = (middle.mem.splice chain (pack result)).live? b :=
      feedforwardMemory_live _ _ (hw.smallRange chain 64 hc) result b
    have hnextwf : next.WF := feedforwardState_wf _ _ _ (hw.wf hwf)
    have hnexttable : ∀ j, j<80 → readBits next.mem (kp.withOffset (BitVec.ofNat 64 (8*j))) 64 = constants.toList.getD j 0 := by
      intro j hj
      rw [readBits_of_live_eq (hnext _), readBits_splice_ne (p := kp.withOffset (BitVec.ofNat 64 (8*j))) _ hck,
        hw.readBits (kp.withOffset (BitVec.ofNat 64 (8*j))) 64 hsk]
      exact htable j hj
    have htail : SmallRange next.mem (data.withOffset 128#64) (128*(n+1)) :=
      ((hw.smallRange data _ hd).feedforward chain result).add (by omega)
    obtain ⟨after, hrun, hawf, haalloc, haglobals, haframe⟩ := ih kp chain stack originalData (data.withOffset 128#64)
      originalCount original result next hnextwf
      ((hw.smallRange chain 64 hc).feedforward chain result)
      ((hw.smallRange stack 128 hs).feedforward chain result) htail
      ((hw.smallRange kp 640 hk).feedforward chain result) hsk hsd hck
      (input_tail_disjoint hd hdis) hnexttable
    have hne : BitVec.ofNat 64 (n+1+1) ≠ 1#64 := by
      intro he
      have h := congrArg BitVec.toNat he
      rw [hcount] at h
      change n+1+1=1 at h
      omega
    have hdec : BitVec.ofNat 64 (n+1+1)-1#64=BitVec.ofNat 64 (n+1) := by
      have he : BitVec.ofNat 64 (n+1+1) = BitVec.ofNat 64 (n+1)+1#64 := by
        rw [← BitVec.ofNat_add]
      rw [he]
      simp
    refine ⟨after, ?_, hawf, haalloc.trans hw.alloc, haglobals.trans hw.globals, ?_⟩
    · rw [hstep, ite_eq_right hne, hdec]
      exact hrun
    · intro b hb
      rw [haframe b hb]
      have hbytes : readBytes next.mem (data.withOffset 128#64) (128*(n+1)) =
          readBytes before.mem (data.withOffset 128#64) (128*(n+1)) := by
        unfold readBytes
        rw [readBits_of_live_eq (hnext _)]
        change readBytes (middle.mem.splice chain (pack result)) (data.withOffset 128#64) (128*(n+1)) = _
        rw [readBytes_splice_disjoint _ chain _ 64 _ _ (input_tail_disjoint hd hdis),
          hw.readBytes (data.withOffset 128#64) (128*(n+1)) hsd]
        rfl
      rw [hbytes, run_readBytes_cons _ _ _ _ hd]
      apply (live_splice_congr chain _ b (hnext b)).trans
      rw [live_splice_splice_self]
      exact live_splice_congr chain _ b (hw.live b (Ne.symm hb))

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core

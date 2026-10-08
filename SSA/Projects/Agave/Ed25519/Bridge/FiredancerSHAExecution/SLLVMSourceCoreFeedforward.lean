import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreValues
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreFeedforwardMemory

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem feedforward_decrement (count : Word) (hn : 0 < count.toNat)
    (hb : count.toNat < 2^63) :
    LLVM.add (.value count) (.value 18446744073709551615#64) {nsw := true} =
      .value (count - 1#64) := by
  have hi : count.toInt = (count.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have hov : count.saddOverflow 18446744073709551615#64 = false := by
    simp only [BitVec.saddOverflow, hi]
    norm_num
    omega
  simp [LLVM.add, LLVM.add?, hov, BitVec.sub_eq_add_neg]

/-- Execute the imported bb4, preserving an arbitrary continuation on its actual jump. -/
theorem feedforward_step (kp chain stack originalData data : Pointer) (originalCount count : Word)
    (original initial work : State) (before : GlobalState)
    (hc : SmallRange before.mem chain 64)
    (hn : 0 < count.toNat) (hb : count.toNat < 2^63)
    {α : Type} (k : HVector TyDenote.toType [] ⊕ SuccArgs core.cfgSigs → EffectM α) :
    StateT.run (core.cfgBlock_3.denote
      (blockInput (feedforwardTarget initial work data count)
        (ambient kp chain stack originalData originalCount original)) >>= fun (_, jump) => k jump) before =
    StateT.run (k (.inr (if count = 1#64 then doneTarget else
      outerTarget (feedForward initial work) (data.withOffset 128#64) (count - 1#64))))
      {before with mem := feedforwardMemory before.mem chain (feedForward initial work)} := by
  simp only [blockInput, feedforwardTarget, ambient]
  unfold core.cfgBlock_3
  have hr0 : Fits before.mem chain 64 := (hc.mono (by decide : 8 ≤ 64)).fits
  denote_step_all v 18
  denote_eval v 18 18
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv18
  subst hv18
  obtain ⟨s1, hs1⟩ : ∃ s : GlobalState, s = {before with mem := before.mem.splice chain (work.a + initial.a)} := ⟨_, rfl⟩
  peel_store (work.a + initial.a), chain, hr0, before as s1 := hs1
  have hc1 : SmallRange s1.mem chain 64 := by rw [hs1]; exact hc.splice chain _
  have hr1 : Fits s1.mem (chain.withOffset 8#64) 64 := (hc1.add (k := 8) (n := 8) (by decide)).fits
  denote_step_all v 19
  denote_eval v 19 19
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv19
  subst hv19
  obtain ⟨s2, hs2⟩ : ∃ s : GlobalState, s = {s1 with mem := s1.mem.splice (chain.withOffset 8#64) (work.b + initial.b)} := ⟨_, rfl⟩
  peel_store (work.b + initial.b), (chain.withOffset 8#64), hr1, s1 as s2 := hs2
  have hc2 : SmallRange s2.mem chain 64 := by rw [hs2]; exact hc1.splice (chain.withOffset 8#64) _
  have hr2 : Fits s2.mem (chain.withOffset 16#64) 64 := (hc2.add (k := 16) (n := 8) (by decide)).fits
  denote_step_all v 20
  denote_eval v 20 20
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv20
  subst hv20
  obtain ⟨s3, hs3⟩ : ∃ s : GlobalState, s = {s2 with mem := s2.mem.splice (chain.withOffset 16#64) (work.c + initial.c)} := ⟨_, rfl⟩
  peel_store (work.c + initial.c), (chain.withOffset 16#64), hr2, s2 as s3 := hs3
  have hc3 : SmallRange s3.mem chain 64 := by rw [hs3]; exact hc2.splice (chain.withOffset 16#64) _
  have hr3 : Fits s3.mem (chain.withOffset 24#64) 64 := (hc3.add (k := 24) (n := 8) (by decide)).fits
  denote_step_all v 21
  denote_eval v 21 21
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv21
  subst hv21
  obtain ⟨s4, hs4⟩ : ∃ s : GlobalState, s = {s3 with mem := s3.mem.splice (chain.withOffset 24#64) (work.d + initial.d)} := ⟨_, rfl⟩
  peel_store (work.d + initial.d), (chain.withOffset 24#64), hr3, s3 as s4 := hs4
  have hc4 : SmallRange s4.mem chain 64 := by rw [hs4]; exact hc3.splice (chain.withOffset 24#64) _
  have hr4 : Fits s4.mem (chain.withOffset 32#64) 64 := (hc4.add (k := 32) (n := 8) (by decide)).fits
  denote_step_all v 22
  denote_eval v 22 22
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv22
  subst hv22
  obtain ⟨s5, hs5⟩ : ∃ s : GlobalState, s = {s4 with mem := s4.mem.splice (chain.withOffset 32#64) (work.e + initial.e)} := ⟨_, rfl⟩
  peel_store (work.e + initial.e), (chain.withOffset 32#64), hr4, s4 as s5 := hs5
  have hc5 : SmallRange s5.mem chain 64 := by rw [hs5]; exact hc4.splice (chain.withOffset 32#64) _
  have hr5 : Fits s5.mem (chain.withOffset 40#64) 64 := (hc5.add (k := 40) (n := 8) (by decide)).fits
  denote_step_all v 23
  denote_eval v 23 23
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv23
  subst hv23
  obtain ⟨s6, hs6⟩ : ∃ s : GlobalState, s = {s5 with mem := s5.mem.splice (chain.withOffset 40#64) (work.f + initial.f)} := ⟨_, rfl⟩
  peel_store (work.f + initial.f), (chain.withOffset 40#64), hr5, s5 as s6 := hs6
  have hc6 : SmallRange s6.mem chain 64 := by rw [hs6]; exact hc5.splice (chain.withOffset 40#64) _
  have hr6 : Fits s6.mem (chain.withOffset 48#64) 64 := (hc6.add (k := 48) (n := 8) (by decide)).fits
  denote_step_all v 24
  denote_eval v 24 24
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv24
  subst hv24
  obtain ⟨s7, hs7⟩ : ∃ s : GlobalState, s = {s6 with mem := s6.mem.splice (chain.withOffset 48#64) (work.g + initial.g)} := ⟨_, rfl⟩
  peel_store (work.g + initial.g), (chain.withOffset 48#64), hr6, s6 as s7 := hs7
  have hc7 : SmallRange s7.mem chain 64 := by rw [hs7]; exact hc6.splice (chain.withOffset 48#64) _
  have hr7 : Fits s7.mem (chain.withOffset 56#64) 64 := (hc7.add (k := 56) (n := 8) (by decide)).fits
  denote_step_all v 25
  denote_eval v 25 25
  simp only [LLVM.add, LLVM.add?, simp_denote, simp_sllvm] at hv25
  subst hv25
  obtain ⟨s8, hs8⟩ : ∃ s : GlobalState, s = {s7 with mem := s7.mem.splice (chain.withOffset 56#64) (work.h + initial.h)} := ⟨_, rfl⟩
  peel_store (work.h + initial.h), (chain.withOffset 56#64), hr7, s7 as s8 := hs8
  denote_step_all v 26
  denote_eval v 26 26
  have hv26' : v26 = .value (data.withOffset 128#64) := by
    simp [hv26, gep, ptradd, Pointer.withOffset,
      LLVM.add, LLVM.mul, LLVM.add?, LLVM.mul?, LLVM.const?, simp_sllvm]
  subst hv26'
  clear hv26
  peel_lifetime
  denote_step_all v 27
  denote_eval v 27 27
  simp only [simp_denote, simp_sllvm, feedforward_decrement count hn hb] at hv27
  subst hv27
  denote_step_all v 28
  denote_eval v 28 28
  simp only [simp_denote, simp_sllvm, LLVM.icmp, LLVM.icmp?] at hv28
  subst hv28
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
  have hstate : s8 = {before with mem := feedforwardMemory before.mem chain (feedForward initial work)} := by
    rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
    simp only [feedforwardMemory, feedForward, BitVec.add_comm]
  rw [hstate]
  have heq : (count - 1#64 == 0#64) = (count == 1#64) := by bv_decide
  simp only [LLVM.icmp', heq]
  by_cases he : count = 1#64
  · rw [ite_eq_left (show BitVec.ofBool (count == 1#64) = 1 from by simp [he]), ite_eq_left he]
    rfl
  · rw [ite_eq_right (show ¬ BitVec.ofBool (count == 1#64) = 1 from by
      rw [show (count == 1#64) = false from beq_eq_false_iff_ne.mpr he]; decide), ite_eq_right he]
    simp only [Target.denote, outerTarget, feedForward, simp_denote, simp_sllvm]
    simp only [BitVec.add_comm]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core

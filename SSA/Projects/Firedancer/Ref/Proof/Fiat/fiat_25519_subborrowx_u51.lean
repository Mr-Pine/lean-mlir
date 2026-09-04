import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_subborrowx_u51
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_subborrowx_u51
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fiat_25519_subborrowx_u51_conforms (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) (hs : s.WF)
    (h₁ : Fits s.mem o₁ 64) (h₂ : Fits s.mem o₂ 8) :
    fiat_25519_subborrowx_u51_spec o₁ o₂ c a b s := by
  simp only [fiat_25519_subborrowx_u51_spec, Cfg.denote]
  obtain ⟨lowv, hlow⟩ : ∃ v : BitVec 64,
      v = a - (BitVec.zeroExtend 64 c + b) &&& 2251799813685247#64 := ⟨_, rfl⟩
  obtain ⟨borrowv, hborrow⟩ : ∃ v : BitVec 8,
      v = 0#8 - BitVec.truncate 8 ((a - (BitVec.zeroExtend 64 c + b)) >>> (51 : Nat)) := ⟨_, rfl⟩
  obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState,
      m = (s.mem.splice o₁ lowv).splice o₂ borrowv := ⟨_, rfl⟩
  rw [← hlow, ← hborrow, ← houtMem]
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case equiv =>
    have hnone : ∀ (q : BlockId), s.alloc.nextFreeBlock ≤ q.id → outMem.live? q = none := by
      rw [houtMem]
      exact fun q hq => live?_splice_eq_none (live?_splice_eq_none (hs q hq))
    exact GlobalState.Equiv.symm
      (GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨rfl, rfl, fun _ => rfl⟩)

  denote_step_all v 6
  denote_eval v 0 6
  simp only [LLVM.const?] at hv0 hv1 hv2
  subst hv0 hv1 hv2
  eval_llvm 3
  eval_llvm 4
  eval_llvm 5
  eval_llvm 6
  have e6 : v6 = .value lowv := by
    rw [hv6, hlow]
  rw [e6]
  peel_store lowv, o₁, h₁, s

  denote_step_all v 9
  denote_eval v 7 9
  eval_llvm 7
  eval_llvm 8
  eval_llvm 9
  have e9 : v9 = .value borrowv := by
    rw [hv9, hborrow]
    exact congrArg PoisonOr.value (by bv_decide)
  rw [e9]
  peel_store borrowv, o₂, (fits_splice h₂), ({ s with mem := s.mem.splice o₁ lowv })
  simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem, simp_denote, simp_sllvm]

end Firedancer.Ref

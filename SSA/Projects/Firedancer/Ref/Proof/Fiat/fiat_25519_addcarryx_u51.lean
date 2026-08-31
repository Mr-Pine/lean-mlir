import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_addcarryx_u51
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_addcarryx_u51
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fiat_25519_addcarryx_u51_conforms (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) (hs : s.WF)
    (h₁ : Fits s.mem o₁ 64) (h₂ : Fits s.mem o₂ 8) :
    fiat_25519_addcarryx_u51_spec o₁ o₂ c a b s := by
  simp only [fiat_25519_addcarryx_u51_spec, Cfg.denote]
  obtain ⟨lowv, hlow⟩ : ∃ v : BitVec 64,
      v = BitVec.zeroExtend 64 c + a + b &&& 2251799813685247#64 := ⟨_, rfl⟩
  obtain ⟨carryv, hcarry⟩ : ∃ v : BitVec 8,
      v = BitVec.truncate 8 ((BitVec.zeroExtend 64 c + a + b) >>> (51 : Nat)) := ⟨_, rfl⟩
  obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState,
      m = (s.mem.splice o₁ lowv).splice o₂ carryv := ⟨_, rfl⟩
  rw [← hlow, ← hcarry, ← houtMem]
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case equiv =>
    have hnone : ∀ (q : BlockId), s.alloc.nextFreeBlock ≤ q.id → outMem.live? q = none := by
      rw [houtMem]
      exact fun q hq => live?_splice_eq_none (live?_splice_eq_none (hs q hq))
    exact GlobalState.Equiv.symm
      (GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨rfl, fun _ => rfl⟩)

  denote_step_all v 7
  denote_eval v 0 7
  simp only [LLVM.const?] at hv0 hv1
  subst hv0 hv1
  eval_llvm 2
  eval_llvm 3
  eval_llvm 4
  eval_llvm 5
  eval_llvm 6
  eval_llvm 7
  have e5 : v5 = .value lowv := by
    rw [hv5, hlow]
  have e7 : v7 = .value carryv := by
    rw [hv7, hcarry]
    exact congrArg PoisonOr.value (by bv_decide)
  rw [e5, e7]
  peel_store lowv, o₁, h₁, s
  peel_store carryv, o₂, (fits_splice h₂), ({ s with mem := s.mem.splice o₁ lowv })
  simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem, simp_denote, simp_sllvm]

end Firedancer.Ref

import SSA.Projects.Firedancer.Ref.Spec.Fiat.fiat_25519_cmovznz_u64
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_cmovznz_u64
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fiat_25519_cmovznz_u64_conforms (o : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) (hs : s.WF) (ho : Fits s.mem o 64) :
    fiat_25519_cmovznz_u64_spec o c a b s := by
  simp only [fiat_25519_cmovznz_u64_spec, Cfg.denote]
  obtain ⟨v, hv⟩ : ∃ v : BitVec 64, v = if c = 0#8 then a else b := ⟨_, rfl⟩
  obtain ⟨outMem, houtMem⟩ : ∃ m : MemoryState, m = s.mem.splice o v := ⟨_, rfl⟩
  rw [← hv, ← houtMem]
  refine ⟨s.popFrame outMem, run_runFunction (s' := { s with mem := outMem }) ?_, ?equiv⟩
  case
    equiv =>
    have hnone : ∀ (q : BlockId), s.alloc.nextFreeBlock ≤ q.id → outMem.live? q = none := by
      rw [houtMem]
      exact fun q hq => live?_splice_eq_none (hs q hq)
    exact
      GlobalState.Equiv.symm
        (GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨rfl, rfl, fun _ => rfl⟩)
  denote_step_all v 2
  denote_eval v 0 2
  simp only [LLVM.const?] at hv0
  subst hv0
  eval_llvm 1
  eval_llvm 2
  have e2 : v2 = .value v := by
    rw [hv2, hv]
    by_cases h : c = 0#8
    · simp [h]
    · simp [h, show (c == 0#8) = false from beq_eq_false_iff_ne.mpr h]
  rw [e2]
  peel_store v, o, ho, s
  simp only [BlockCom.denote_term, Terminator.denote_ret, houtMem, simp_denote, simp_sllvm]

end Firedancer.Ref

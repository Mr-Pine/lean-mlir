import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_neg
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_opp

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_f25519_neg_conforms (o q : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o)
    (hq : IsFieldElemPtr s.mem q)
    (hqbounds : LimbBounds hq) :
    fd_f25519_neg_spec o q s ho hq := by
  simp only [fd_f25519_neg_spec, Cfg.denote]

  obtain ⟨out, hval, hbounds, oppstate, hoppstate, hoppstate_eq⟩ :=
    fiat_25519_opp_conforms o q s hs ho hq hqbounds

  have hoppWF : oppstate.WF := GlobalState.WF.of_equiv hs.splice hoppstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → oppstate.mem.live? t = none := by
    rw [hoppstate_eq.1]; exact hoppWF
  have hpop : (s.popFrame oppstate.mem : GlobalState) ≈ oppstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨hoppstate_eq.1, hoppstate_eq.globals, fun _ => rfl⟩

  refine ⟨out, hval, hbounds, s.popFrame oppstate.mem, ?_,
    GlobalState.Equiv.trans hoppstate_eq (GlobalState.Equiv.symm hpop)⟩

  refine run_runFunction (s' := oppstate) ?_

  refine (BlockCom.run_bind_denote_call_of_nil (s' := oppstate) ?_).trans ?_
  · exact hoppstate

  rfl

end Firedancer.Ref

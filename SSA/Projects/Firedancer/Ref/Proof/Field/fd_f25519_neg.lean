import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_neg
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_opp

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_f25519_neg_conforms (o q : Pointer) (s : GlobalState)
    (hs : s.WF)
    (hqbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x8000000000000)
    (ho : IsFieldElemPtr s.mem o)
    (hq : IsFieldElemPtr s.mem q) :
    fd_f25519_neg_spec o q s := by
  simp only [fd_f25519_neg_spec, Cfg.denote]

  obtain ⟨out, ⟨oppstate, hoppstate, hoppstate_eq⟩, hval, hbounds⟩ :=
    fiat_25519_opp_conforms o q s hs hqbounds ho hq

  have hoppWF : oppstate.WF := GlobalState.WF.of_equiv hs.splice hoppstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → oppstate.mem.live? t = none := by
    rw [hoppstate_eq.1]; exact hoppWF
  have hpop : (s.popFrame oppstate.mem : GlobalState) ≈ oppstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨hoppstate_eq.1, fun _ => rfl⟩

  refine ⟨out, ⟨s.popFrame oppstate.mem, ?_,
    GlobalState.Equiv.trans hoppstate_eq (GlobalState.Equiv.symm hpop)⟩, hval, hbounds⟩

  refine run_runFunction (s' := oppstate) ?_

  refine (BlockCom.run_bind_denote_call_of_nil (s' := oppstate) ?_).trans ?_
  · exact hoppstate

  rfl

end Firedancer.Ref

import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_sqr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_carry_square

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_f25519_sqr_conforms (o p : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o)
    (hp : IsFieldElemPtr s.mem p)
    (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_sqr_spec o p s ho hp := by
  simp only [fd_f25519_sqr_spec, Cfg.denote]

  obtain ⟨out, hout, hbounds, ⟨sqrstate, hsqrstate, hsqrstate_eq⟩⟩ :=
    fiat_25519_carry_square_conforms o p s hs ho hp hplimb

  have hsqrWF : sqrstate.WF := GlobalState.WF.of_equiv hs.splice hsqrstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → sqrstate.mem.live? t = none := by
    rw [hsqrstate_eq.1]; exact hsqrWF
  have hpop : (s.popFrame sqrstate.mem : GlobalState) ≈ sqrstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨hsqrstate_eq.1, fun _ => rfl⟩

  refine ⟨out, hout, hbounds, ⟨s.popFrame sqrstate.mem, ?_,
    GlobalState.Equiv.trans hsqrstate_eq (GlobalState.Equiv.symm hpop)⟩⟩

  refine run_runFunction (s' := sqrstate) ?_

  refine (BlockCom.run_bind_denote_call_of_nil (s' := sqrstate) ?_).trans ?_
  · exact hsqrstate

  rfl

end Firedancer.Ref

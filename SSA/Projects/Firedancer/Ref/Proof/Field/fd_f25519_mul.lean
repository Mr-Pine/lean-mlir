import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_mul
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_carry_mul

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_f25519_mul_conforms (o p q : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o)
    (hp : IsFieldElemPtr s.mem p)
    (hq : IsFieldElemPtr s.mem q)
    (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000)
    (hqlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_mul_spec o p q s ho hp hq := by
  simp only [fd_f25519_mul_spec, Cfg.denote]

  obtain ⟨out, hout, ⟨mulstate, hmulstate, hmulstate_eq⟩, hbounds⟩ :=
    fiat_25519_carry_mul_conforms o p q s hs ho hp hq hplimb hqlimb

  have hmulWF : mulstate.WF := GlobalState.WF.of_equiv hs.splice hmulstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → mulstate.mem.live? t = none := by
    rw [hmulstate_eq.1]; exact hmulWF
  have hpop : (s.popFrame mulstate.mem : GlobalState) ≈ mulstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨hmulstate_eq.1, hmulstate_eq.globals, fun _ => rfl⟩

  -- the fiat callee states its result as the limbs it wrote; read them back
  refine ⟨out, (readFieldElem_eq_of (readFieldElem?_splice out ho.left)).trans hout,
    limbBounds_of_readLimb? _ hbounds,
    ⟨s.popFrame mulstate.mem, ?_,
      GlobalState.Equiv.trans hmulstate_eq (GlobalState.Equiv.symm hpop)⟩⟩

  refine run_runFunction (s' := mulstate) ?_

  refine (BlockCom.run_bind_denote_call_of_nil (s' := mulstate) ?_).trans ?_
  · exact hmulstate

  rfl

end Firedancer.Ref

import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_sqr
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_sqr
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_carry_square

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_f25519_sqr_conforms`, plus: all-zero limbs at `o` come only from an all-zero operand. -/
theorem fd_f25519_sqr_conforms' (o p : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p)
    (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_sqr_spec o p s ho hp ∧
      ∀ s' : GlobalState,
        StateT.run
              (runFunction (fd_f25519_sqr.denote (Ctxt.Valuation.ofHVector [.value p, .value o]ₕ)))
              s =
            .value ([.value o]ₕ, s') →
          ZeroLimbs o s'.mem → ZeroLimbs p s.mem := by
  obtain ⟨out, hout, hbounds, ⟨sqrstate, hsqrstate, hsqrstate_eq⟩, hzero⟩ :=
    fiat_25519_carry_square_conforms o p s hs ho hp hplimb
  have hsqrWF : sqrstate.WF := GlobalState.WF.of_equiv hs.splice hsqrstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → sqrstate.mem.live? t = none := by
    rw [hsqrstate_eq.1]; exact hsqrWF
  have hpop : (s.popFrame sqrstate.mem : GlobalState) ≈ sqrstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone)
      ⟨hsqrstate_eq.1, hsqrstate_eq.globals, fun _ => rfl⟩
  have hrun :
    StateT.run (runFunction (fd_f25519_sqr.denote (Ctxt.Valuation.ofHVector [.value p, .value o]ₕ)))
        s =
      .value ([.value o]ₕ, s.popFrame sqrstate.mem) := by
    simp only [Cfg.denote]
    refine run_runFunction (s' := sqrstate) ?_
    refine (BlockCom.run_bind_denote_call_of_nil (s' := sqrstate) ?_).trans ?_
    · exact hsqrstate
    rfl
  refine
    ⟨⟨out, hout, hbounds,
        ⟨s.popFrame sqrstate.mem, hrun,
          GlobalState.Equiv.trans hsqrstate_eq (GlobalState.Equiv.symm hpop)⟩⟩,
      fun s' h hz => hzero ?_⟩
  rw [hrun] at h
  replace h := (Prod.mk.inj (PoisonOr.value_inj.mp h)).2
  exact
    ZeroLimbs.of_equiv (GlobalState.Equiv.trans hsqrstate_eq (GlobalState.Equiv.symm hpop)) (h ▸ hz)

theorem fd_f25519_sqr_conforms (o p : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p)
    (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_sqr_spec o p s ho hp :=
  (fd_f25519_sqr_conforms' o p s hs ho hp hplimb).1

end Firedancer.Ref

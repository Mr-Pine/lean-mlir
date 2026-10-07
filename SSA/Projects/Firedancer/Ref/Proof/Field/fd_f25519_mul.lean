module

public import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_mul
public import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_mul
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

public import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_carry_mul

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_f25519_mul_conforms`, plus: all-zero limbs at `o` come only from an all-zero operand. -/
theorem fd_f25519_mul_conforms' (o p q : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q)
    (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000)
    (hqlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_mul_spec o p q s ho hp hq ∧
      ∀ s' : GlobalState,
        StateT.run
              (runFunction
                (fd_f25519_mul.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ)))
              s =
            .value ([.value o]ₕ, s') →
          ZeroLimbs o s'.mem → ZeroLimbs p s.mem ∨ ZeroLimbs q s.mem := by
  obtain ⟨out, hout, ⟨mulstate, hmulstate, hmulstate_eq⟩, hbounds, hzero⟩ :=
    fiat_25519_carry_mul_conforms o p q s hs ho hp hq hplimb hqlimb
  have hmulWF : mulstate.WF := GlobalState.WF.of_equiv hs.splice hmulstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → mulstate.mem.live? t = none := by
    rw [hmulstate_eq.1]; exact hmulWF
  have hpop : (s.popFrame mulstate.mem : GlobalState) ≈ mulstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone)
      ⟨hmulstate_eq.1, hmulstate_eq.globals, fun _ => rfl⟩
  have hrun :
    StateT.run
        (runFunction
          (fd_f25519_mul.denote (Ctxt.Valuation.ofHVector [.value q, .value p, .value o]ₕ)))
        s =
      .value ([.value o]ₕ, s.popFrame mulstate.mem) := by
    simp only [Cfg.denote]
    refine run_runFunction (s' := mulstate) ?_
    refine (BlockCom.run_bind_denote_call_of_nil (s' := mulstate) ?_).trans ?_
    · exact hmulstate
    rfl
  refine ⟨?_, fun s' h hz => hzero ?_⟩
  · -- the fiat callee states its result as the limbs it wrote; read them back
    exact
      ⟨out, (readFieldElem_eq_of (readFieldElem?_splice out ho.left)).trans hout,
        limbBounds_of_readLimb? _ hbounds,
        ⟨s.popFrame mulstate.mem, hrun,
          GlobalState.Equiv.trans hmulstate_eq (GlobalState.Equiv.symm hpop)⟩⟩
  · rw [hrun] at h
    replace h := (Prod.mk.inj (PoisonOr.value_inj.mp h)).2
    exact
      ZeroLimbs.of_equiv (GlobalState.Equiv.trans hmulstate_eq (GlobalState.Equiv.symm hpop))
        (h ▸ hz)

theorem fd_f25519_mul_conforms (o p q : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q)
    (hplimb : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x18000000000000)
    (hqlimb : ∀ (i : Fin 5) (l : ℕ), readLimb? q i s.mem = some l → l ≤ 0x18000000000000) :
    fd_f25519_mul_spec o p q s ho hp hq :=
  (fd_f25519_mul_conforms' o p q s hs ho hp hq hplimb hqlimb).1

end Firedancer.Ref

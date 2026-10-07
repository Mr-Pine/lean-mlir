module

public import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_neg
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

public import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_opp

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_f25519_neg_conforms`, plus the limbs: `o` holds `bias - q` limbwise. -/
theorem fd_f25519_neg_conforms' (o q : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (hq : IsFieldElemPtr s.mem q) (hqbounds : BiasBounds hq) :
    fd_f25519_neg_spec o q s ho hq ∧
      ∀ s' : GlobalState,
        StateT.run
              (runFunction (fd_f25519_neg.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ)))
              s =
            .value ([.value o]ₕ, s') →
          ∀ i, readLimb? o i s'.mem = some (biasLimb i - readLimb i hq) := by
  obtain ⟨out, hval, hbounds, ⟨oppstate, hoppstate, hoppstate_eq⟩, hlimbs⟩ :=
    fiat_25519_opp_conforms o q s hs ho hq hqbounds
  have hoppWF : oppstate.WF := GlobalState.WF.of_equiv hs.splice hoppstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → oppstate.mem.live? t = none := by
    rw [hoppstate_eq.1]; exact hoppWF
  have hpop : (s.popFrame oppstate.mem : GlobalState) ≈ oppstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone)
      ⟨hoppstate_eq.1, hoppstate_eq.globals, fun _ => rfl⟩
  have hrun :
    StateT.run (runFunction (fd_f25519_neg.denote (Ctxt.Valuation.ofHVector [.value q, .value o]ₕ)))
        s =
      .value ([.value o]ₕ, s.popFrame oppstate.mem) := by
    simp only [Cfg.denote]
    refine run_runFunction (s' := oppstate) ?_
    refine (BlockCom.run_bind_denote_call_of_nil (s' := oppstate) ?_).trans ?_
    · exact hoppstate
    rfl
  refine
    ⟨⟨out, hval, hbounds, s.popFrame oppstate.mem, hrun,
        GlobalState.Equiv.trans hoppstate_eq (GlobalState.Equiv.symm hpop)⟩,
      fun s' h i => ?_⟩
  rw [hrun] at h
  replace h := (Prod.mk.inj (PoisonOr.value_inj.mp h)).2
  rw [← h, ←
    readLimb?_of_equiv (GlobalState.Equiv.trans hoppstate_eq (GlobalState.Equiv.symm hpop)) o i]
  exact hlimbs i

theorem fd_f25519_neg_conforms (o q : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (hq : IsFieldElemPtr s.mem q) (hqbounds : BiasBounds hq) :
    fd_f25519_neg_spec o q s ho hq :=
  (fd_f25519_neg_conforms' o q s hs ho hq hqbounds).1

end Firedancer.Ref

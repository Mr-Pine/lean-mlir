module

public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_eq_z1
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Memory
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Avx512.Proof.Common
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_eq

@[expose] public section


namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_ed25519_point_eq_z1_conforms (p q: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hp : IsQuadPtr s.mem p)
  (hq : IsQuadPtr s.mem q)
  (hpU46 : (readQuad hp).U46)
  (hqU46 : (readQuad hq).U46)
  (hpzUnit : IsUnit (readQuad hp).toPoint.Z) :
  fd_ed25519_point_eq_z1_spec p q s hp hq := by
    intro hz1
    simp only [Cfg.denote]

    obtain ⟨eqstate, heqstate, heqstate_eq⟩ :=
      fd_ed25519_point_eq_conforms p q s hs hp hq hpU46 hqU46 hpzUnit
        (by rw [hz1]; exact isUnit_one)

    refine ⟨s.popFrame eqstate.mem, run_runFunction (s' := eqstate) ?_, GlobalState.Equiv.symm
      (GlobalState.killFrom_equiv eqstate.mem hs fun b _ => (heqstate_eq.live b).symm)⟩

    -- the entry is just the call: expose its constructor first
    unfold fd_ed25519_point_eq_z1
    dsimp only
    peel_call heqstate
    simp_return

end Firedancer.Avx512

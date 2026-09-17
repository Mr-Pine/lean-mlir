/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_add_final_mul
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_set

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_ed25519_point_add_final_mul_conforms (r a : Pointer) (s : GlobalState) (hs : s.WF)
    (hne : r.id ≠ a.id) (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) :
    fd_ed25519_point_add_final_mul_spec r a s hne hr ha := by
  simp only [fd_ed25519_point_add_final_mul_spec, Cfg.denote]
  obtain ⟨st, hrun, heq⟩ := fd_ed25519_point_set_conforms r a s hs hne hr ha
  refine ⟨s.popFrame st.mem, run_runFunction (s' := st) ?run, ?equiv⟩
  -- no allocas, so `popFrame` kills no live block
  case equiv =>
    have hout : ({ s with mem := s.mem.writeQuad r (readQuad ha) } : GlobalState).WF :=
      fun q hq => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (hs q hq)))
    have hst : st.WF := hout.of_equiv heq
    have halloc : s.alloc = st.alloc := heq.1
    have hpop : (s.popFrame st.mem : GlobalState) ≈ st :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none fun q hq => hst q (halloc ▸ hq))
        ⟨halloc, heq.globals, fun _ => rfl⟩
    exact GlobalState.Equiv.trans heq (GlobalState.Equiv.symm hpop)
  case run =>
    unfold fd_ed25519_point_add_final_mul
    dsimp only
    peel_call hrun
    simp_return

end Firedancer.Avx512

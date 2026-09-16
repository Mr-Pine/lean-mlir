/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_sub_nr
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_sub

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_f25519_sub_nr_conforms (o p q : Pointer) (s : GlobalState) (hs : s.WF)
    (hpbounds : ∀ (i : Fin 5) (l : ℕ), readLimb? p i s.mem = some l → l ≤ 0x8000000000000)
    (hqbounds : BiasBounds? q s.mem)
    (ho : IsFieldElemPtr s.mem o) (hp : IsFieldElemPtr s.mem p) (hq : IsFieldElemPtr s.mem q) :
    fd_f25519_sub_nr_spec o p q s ho hp hq := by
  simp only [fd_f25519_sub_nr_spec, Cfg.denote]
  obtain ⟨out, hout, hbounds, ⟨st, hst, hst_eq⟩, -⟩ :=
    fiat_25519_sub_conforms o p q s hs hpbounds hqbounds ho hp hq
  have hWF : st.WF := GlobalState.WF.of_equiv hs.splice hst_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → st.mem.live? t = none := by
    rw [hst_eq.1]; exact hWF
  have hpop : (s.popFrame st.mem : GlobalState) ≈ st :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨hst_eq.1, hst_eq.globals, fun _ => rfl⟩
  refine ⟨out, hout, hbounds,
    ⟨s.popFrame st.mem, ?_, GlobalState.Equiv.trans hst_eq (GlobalState.Equiv.symm hpop)⟩⟩
  refine run_runFunction (s' := st) ?_
  refine (BlockCom.run_bind_denote_call_of_nil (s' := st) ?_).trans ?_
  · exact hst
  rfl

end Firedancer.Ref

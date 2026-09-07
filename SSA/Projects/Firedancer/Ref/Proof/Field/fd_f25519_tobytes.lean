import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_tobytes
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_to_bytes

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The wrapper adds nothing to the callee: one void call, then `return %arg0`.
`fiat_25519_to_bytes`'s two preconditions -- the per-limb bias bounds and the
sum bound -- are passed straight through. -/
theorem fd_f25519_tobytes_conforms (o q : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ho : IsByteBufPtr s.mem o)
    (hq : IsFieldElemPtr s.mem q)
    (hqlimb : BiasBounds hq) (hqlt : limbSum hq < 2 ^ 256 - 38) :
    fd_f25519_tobytes_spec o q s ho hq := by
  simp only [fd_f25519_tobytes_spec, Cfg.denote]

  obtain ⟨out, hout, ⟨tostate, htostate, htostate_eq⟩⟩ :=
    fiat_25519_to_bytes_conforms o q s hs ho hq hqlimb hqlt

  have htoWF : tostate.WF := GlobalState.WF.of_equiv hs.splice htostate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → tostate.mem.live? t = none := by
    rw [htostate_eq.1]; exact htoWF
  have hpop : (s.popFrame tostate.mem : GlobalState) ≈ tostate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone)
      ⟨htostate_eq.1, htostate_eq.globals, fun _ => rfl⟩

  refine ⟨out, hout, ⟨s.popFrame tostate.mem, ?_,
    GlobalState.Equiv.trans htostate_eq (GlobalState.Equiv.symm hpop)⟩⟩

  refine run_runFunction (s' := tostate) ?_

  refine (BlockCom.run_bind_denote_call_of_nil (s' := tostate) ?_).trans ?_
  · exact htostate

  rfl

end Firedancer.Ref

import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_frombytes
import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_frombytes
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_from_bytes

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_f25519_frombytes_conforms (o p : Pointer) (s : GlobalState)
    (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o)
    (hp : IsByteBufPtr s.mem p) :
    fd_f25519_frombytes_spec o p s ho hp := by
  simp only [fd_f25519_frombytes_spec, Cfg.denote]

  obtain ⟨out, hout, hbounds, ⟨decstate, hdecstate, hdecstate_eq⟩⟩ :=
    fiat_25519_from_bytes_conforms o p s hs ho hp

  have hdecWF : decstate.WF := GlobalState.WF.of_equiv hs.splice hdecstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → decstate.mem.live? t = none := by
    rw [hdecstate_eq.1]; exact hdecWF
  have hpop : (s.popFrame decstate.mem : GlobalState) ≈ decstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone) ⟨hdecstate_eq.1, hdecstate_eq.globals, fun _ => rfl⟩

  refine ⟨out, hout, hbounds, ⟨s.popFrame decstate.mem, ?_,
    GlobalState.Equiv.trans hdecstate_eq (GlobalState.Equiv.symm hpop)⟩⟩

  refine run_runFunction (s' := decstate) ?_

  refine (BlockCom.run_bind_denote_call_of_nil (s' := decstate) ?_).trans ?_
  · exact hdecstate

  rfl

end Firedancer.Ref

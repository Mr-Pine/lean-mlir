module

public import SSA.Projects.Firedancer.Ref.Spec.Field.fd_f25519_if
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

public import SSA.Projects.Firedancer.Ref.Proof.Fiat.fiat_25519_selectznz

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The wrapper truncates `cond` to a byte and calls `fiat_25519_selectznz`
with the operands swapped, so the conformance is the callee's with
`x := a1`, `y := a0`. -/
theorem fd_f25519_if_conforms (r : Pointer) (cond : BitVec 32) (a0 a1 : Pointer) (s : GlobalState)
    (hs : s.WF) (hr : IsFieldElemPtr s.mem r) (h0 : IsFieldElemPtr s.mem a0)
    (h1 : IsFieldElemPtr s.mem a1) : fd_f25519_if_spec r cond a0 a1 s hr h0 h1 := by
  -- `ite_not` re-orients the spec's `cond ≠ 0` branch onto the callee's `c = 0`
  simp only [fd_f25519_if_spec, Cfg.denote, ne_eq, ite_not]
  obtain ⟨hselval, selstate, hselstate, hselstate_eq⟩ :=
    fiat_25519_selectznz_conforms r (cond.setWidth 8) a1 a0 s hs hr h1 h0
  refine ⟨hselval, ?_⟩
  have hselWF : selstate.WF := GlobalState.WF.of_equiv hs.splice hselstate_eq
  have hnone : ∀ t : BlockId, s.alloc.nextFreeBlock ≤ t.id → selstate.mem.live? t = none := by
    rw [hselstate_eq.1]; exact hselWF
  have hpop : (s.popFrame selstate.mem : GlobalState) ≈ selstate :=
    GlobalState.Equiv.trans (killFrom_equiv_of_none hnone)
      ⟨hselstate_eq.1, hselstate_eq.globals, fun _ => rfl⟩
  refine
    ⟨s.popFrame selstate.mem, run_runFunction (s' := selstate) ?run,
      GlobalState.Equiv.trans hselstate_eq (GlobalState.Equiv.symm hpop)⟩
  case run =>
    -- %0 = trunc %arg1 : i32 to i8
    denote_step_all v 0
    denote_eval v 0 0
    eval_llvm 0
    subst hv0
    peel_call hselstate
    simp_return

end Firedancer.Ref

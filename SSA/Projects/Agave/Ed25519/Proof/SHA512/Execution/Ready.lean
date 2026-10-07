import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ContextContracts
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Linked

/-! The concrete Montgomery-table prerequisite is preserved by private-frame
work. It is not folded into an unrestricted scalar-reducer assumption. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR

/-- If erasing a private frame gives the original memory, every original
immutable global retains its exact allocation and byte initializer. -/
theorem present_of_frame (g : ByteGlobal) (id : BlockId) (before after : MemoryState)
    (mark : Nat) (hframe : after.eraseFrom mark = before)
    (h : g.Present id before) : g.Present id after := by
  unfold ByteGlobal.Present at *
  rw [← hframe] at h
  have heq : (after.eraseFrom mark)[id]? =
      after[id]?.filter (fun _ => decide (id.id < mark)) := by
    simp [MemoryState.eraseFrom, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_filter']
  rw [heq] at h
  exact Option.eq_some_of_filter_eq_some h

/-- This instantiates the contextual finalizer contract with the actual
wide reducer's two fixed global addresses. No primitive execution is assumed
by this preservation theorem. -/
theorem ready_of_frame (g : ScalarWide.Globals) (before after : GlobalState)
    (out : Pointer) (mark : Nat) (hframe : after.mem.eraseFrom mark = before.mem)
    (h : ScalarWide.Ready g before out) : ScalarWide.Ready g after out := by
  obtain ⟨h0, h1, hr, hrr, hne, ho0, ho1⟩ := h
  exact ⟨h0, h1, present_of_frame _ _ _ _ _ hframe hr,
    present_of_frame _ _ _ _ _ hframe hrr, hne, ho0, ho1⟩

/-- A local concrete reducer obligation: only states satisfying the actual
Montgomery-table invariant are quantified over. -/
def LinkedReduceWideContract (g : ScalarWide.Globals) : Prop :=
  ReduceWideContractUnder (ScalarWide.Ready g) (ScalarWide.linkedProgram g).call

/-- The exact linked reducer execution obligation supplies the local ABI
needed by the finalizer; the reducer body remains a separate proof obligation. -/
theorem linkedReduceWide_of_execution (g : ScalarWide.Globals)
    (h : ScalarWide.ExecutionObligation g) : LinkedReduceWideContract g := by
  intro state dst src hwf hr hd hs hdis
  obtain ⟨after, hcall, heffect, _⟩ :=
    ScalarWide.store_effect_of_exact_execution g h state dst src hwf hr hd hs hdis
  exact ⟨after, hcall, heffect⟩

end Agave.Ed25519.Verifier.Execution.SHA512Finalization

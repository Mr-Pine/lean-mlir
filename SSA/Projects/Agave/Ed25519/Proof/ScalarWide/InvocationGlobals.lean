import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.GlobalOperands

/-! Recover immutable global facts from exact erasure of invocation-local writes. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR

/-- Below the frame boundary, erased and original maps have identical entries. -/
theorem block_of_erase (mem base : MemoryState) (mark : Nat)
    (hframe : mem.eraseFrom mark = base) (id : BlockId) (hlt : id.id < mark) :
    mem[id]? = base[id]? := by
  rw [← hframe]
  simp [MemoryState.eraseFrom, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_filter', hlt]
  cases mem.mem[id]? <;> rfl

theorem ready_of_erase (g : Globals) (state after : GlobalState) (out : Pointer)
    (hwf : state.WF) (hr : Ready g state out)
    (hframe : after.mem.eraseFrom state.alloc.nextFreeBlock = state.mem) :
    Ready g after out := by
  have h0 := hwf.lt (ready_r_range g state out hr).fits.mem
  have h1 := hwf.lt (ready_rr_range g state out hr).fits.mem
  refine ⟨hr.1, hr.2.1, ?_, ?_, hr.2.2.2.2⟩
  · change after.mem[g.address0.id]? = _
    rw [block_of_erase after.mem state.mem state.alloc.nextFreeBlock hframe g.address0.id h0]
    exact hr.2.2.1
  · change after.mem[g.address1.id]? = _
    rw [block_of_erase after.mem state.mem state.alloc.nextFreeBlock hframe g.address1.id h1]
    exact hr.2.2.2.1

end Agave.Ed25519.Verifier.Execution.ScalarWide

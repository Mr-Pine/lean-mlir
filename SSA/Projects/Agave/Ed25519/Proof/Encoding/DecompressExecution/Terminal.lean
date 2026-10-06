import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Program
import SSA.Projects.RIR.Run.Tactic
import SSA.Projects.RIR.Run.Memory

/-! Execution of the actual common return block, including the Option tag store.
Reaching this block with tag 0 or 1 is a separate obligation for the entry and
success blocks. No payload read is needed on rejection. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open LeanMLIR.RIR

/-- The common return block writes exactly its incoming tag and returns. -/
theorem terminal_block (E : ⟪program.Γ⟫) (out : Pointer) (tag : BitVec 64)
    (s : GlobalState) (hfits : Fits s.mem out 64)
    (hout : E.read (%arg0) = .value out) (htag : E.read (%141) = .value tag) :
    program.bb2.run program.blockParams E s =
      .value ((E, .inl .nil), {s with mem := s.mem.storeAt out tag}) := by
  have hstore := run_store (env := E) hfits
    (show Ty.flatten (.bv 64) (.value tag) = .value tag from rfl)
  simp [BasicBlock.run, program.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    hout, htag, hstore, Exit.run, Regs.read_nil]

/-- Actual RIR continuation after either incoming edge to the Option tag store. -/
theorem terminal_run (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (out : Pointer) (tag : BitVec 64) (s : GlobalState) (hfits : Fits s.mem out 64)
    (hout : E.read (%arg0) = .value out) (htag : E.read (%141) = .value tag) :
    (program p g).runFrom E 2 s =
      .value (.nil, {s with mem := s.mem.storeAt out tag}) := by
  rw [Func.runFrom_eq]
  change (do
    let ((E', res), s') ← program.bb2.run program.blockParams E s
    Func.continue (func := program p g) E' res s') = _
  rw [terminal_block E out tag s hfits hout htag]
  rfl

end Agave.Ed25519.Encoding.Decompress.Execution.Decode

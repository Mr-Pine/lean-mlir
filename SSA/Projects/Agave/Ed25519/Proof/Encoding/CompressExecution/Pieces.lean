import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Program
import SSA.Projects.RIR.Run.Tactic

/-! Cut points in the original single basic block. No instructions are replaced
or abstracted: each slice is a take/drop of the imported instruction list. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Execute exactly `count` original instructions starting at `first`. -/
def runSlice (p : Primitives) (first count : Nat) (E : Env program.Γ) :
    EffectM (Env program.Γ) :=
  List.foldlM Instr.run E (((program.entry p).body.drop first).take count)

/-- The original remaining instructions followed by its empty return. -/
def finishFrom (p : Primitives) (first : Nat) (E : Env program.Γ) : EffectM (Vals []) := do
  let _ ← (program.entry p).runBodyFrom E first
  pure .nil

theorem finishFrom_zero (p : Primitives) (E : Env program.Γ) (s : GlobalState) :
    (program p).runFrom E 0 s = finishFrom p 0 E s := by
  rw [Func.runFrom_eq]
  simp [BasicBlock.run, finishFrom, BasicBlock.runBodyFrom, program.entry,
    Exit.run, Regs.read_nil, EffectM.bind_eq, EffectM.pure_eq, Func.continue]

/-- Compose a checked finite prefix with the actual remaining instructions. -/
theorem finishFrom_of_slice (p : Primitives) (first count : Nat)
    (E F : Env program.Γ) (s t : GlobalState)
    (h : runSlice p first count E s = .value (F, t)) :
    finishFrom p first E s = finishFrom p (first + count) F t := by
  have hsplit : (program.entry p).body.drop first =
      ((program.entry p).body.drop first).take count ++
        (program.entry p).body.drop (first + count) := by
    rw [← List.drop_drop]
    exact (List.take_append_drop count _).symm
  simp only [finishFrom, BasicBlock.runBodyFrom]
  conv => lhs; rw [hsplit]
  simp only [List.foldlM_append, EffectM.bind_eq, bind_assoc]
  change (runSlice p first count E s >>= fun (E', s') =>
    finishFrom p (first + count) E' s') = _
  rw [h]
  rfl

end Agave.Ed25519.Encoding.Compress.Execution

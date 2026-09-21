module

public import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR

public section

def BasicBlock.runBodyFrom (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫) (n : Nat) : EffectM ⟪Γ⟫ :=
  List.foldlM Instr.run env (block.body.drop n)

theorem BasicBlock.runBodyFrom_zero (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫) :
    block.runBodyFrom env 0 = List.foldlM Instr.run env block.body := by rfl

theorem BasicBlock.runBodyFrom_step (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫)
    (hpos : pos < block.body.length := by decide) :
    block.runBodyFrom env pos =
      (do
        let E' ← Instr.run env (block.body[pos]'hpos)
        block.runBodyFrom E' (pos + 1)) := by
  rw [runBodyFrom, List.drop_eq_getElem_cons hpos, List.foldlM_cons]
  rfl

theorem BasicBlock.runBodyFrom_step_pure (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫)
    (hpos : pos < block.body.length := by decide)
    (h : Instr.run env (block.body[pos]'hpos) = pure E') :
    block.runBodyFrom env pos = block.runBodyFrom E' (pos + 1) := by
  rw [runBodyFrom_step _ _ hpos, h]
  rfl

theorem BasicBlock.runBodyFrom_done (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫)
    (hpos : pos ≥ block.body.length := by decide) : block.runBodyFrom env pos = pure env := by
  rw [runBodyFrom, List.drop_eq_nil_of_le hpos, List.foldlM_nil]

theorem BasicBlock.run_eq (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫) :
    block.run env = block.runBodyFrom env 0 >>= fun E => (E, ·) <$> block.exit.run E := by
  rw [runBodyFrom_zero, run]
  rfl

end

end LeanMLIR.RIR

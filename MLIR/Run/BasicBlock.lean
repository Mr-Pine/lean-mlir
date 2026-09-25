module

public import MLIR.Semantics.Func

namespace MLIR

public section

def BasicBlock.runBodyFrom (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫) (n : Nat) : EffectM ⟪Γ⟫ :=
  List.foldlM Instr.run env (block.body.drop n)

private theorem BasicBlock.runBodyFrom_zero (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫) :
    block.runBodyFrom env 0 = List.foldlM Instr.run env block.body := by rfl

theorem BasicBlock.runBodyFrom_step (block : BasicBlock Γ tRets bp) (env : ⟪Γ⟫)
    (hpos : pos < block.body.length := by decide) :
    block.runBodyFrom env pos =
      (do
        let E' ← Instr.run env (block.body[pos]'hpos)
        block.runBodyFrom E' (pos + 1)) := by
  rw [runBodyFrom, List.drop_eq_getElem_cons hpos, List.foldlM_cons]
  rfl

theorem BasicBlock.runBodyFrom_step_pure {block : BasicBlock Γ tRets bp} {env : ⟪Γ⟫}
    (hpos : pos < block.body.length := by decide)
    (h : Instr.run env (block.body[pos]'hpos) = pure E') :
    block.runBodyFrom env pos = block.runBodyFrom E' (pos + 1) := by
  rw [runBodyFrom_step _ _ hpos, h]
  rfl

theorem BasicBlock.runBodyFrom_done {block : BasicBlock Γ tRets bp} {env : ⟪Γ⟫}
    (hpos : pos ≥ block.body.length := by decide) : block.runBodyFrom env pos = pure env := by
  rw [runBodyFrom, List.drop_eq_nil_of_le hpos, List.foldlM_nil]

theorem BasicBlock.run_eq {bt : Fin n → List Ty} (block : BasicBlock Γ tRets bt)
    (params : (k : Fin n) → Dsts Γ (bt k)) (env : ⟪Γ⟫) :
    block.run params env = block.runBodyFrom env 0 >>= block.exit.run params := by
  rw [runBodyFrom_zero, run]

theorem BasicBlock.runBodyFrom_step_of_run {block : BasicBlock Γ tRets bp} {env : ⟪Γ⟫}
    (hpos : pos < block.body.length := by decide)
    (h : Instr.run env (block.body[pos]'hpos) s = .value (E', s')) :
    block.runBodyFrom env pos s = block.runBodyFrom E' (pos + 1) s' := by
  rw [runBodyFrom_step _ _ hpos]
  simp [h]

open Lean Meta in
/-- Reduce `b.body[i]` when both the block and the index are concrete. -/
dsimproc [simp, mlir_instr]reduceBodyGetElem ((BasicBlock.body _)[_]) := fun e => do
  let e' ← withTransparency .default (whnf e)
  if e' == e then
    return .continue
  else
    return .visit e'

open Lean Meta in
/-- Reduce `tys[i]` to a type when the list and the index are concrete. -/
dsimproc [simp, mlir_instr]reduceTyGetElem ((_ : List Ty)[_]) := fun e => do
  let e' ← withTransparency .default (whnf e)
  match_expr e' with
  | Ty.bv _ =>
    return .visit e'
  | Ty.ptr =>
    return .visit e'
  | _ =>
    return .continue

section ControlFlow

/-- Running a jump chosen by an `if` runs the chosen jump. -/
theorem Jump.run_ite {c : Prop} [Decidable c] {bt : Fin n → List Ty}
    (params : (k : Fin n) → Dsts Γ (bt k)) (env : ⟪Γ⟫) (j j' : Jump Γ bt) :
    Jump.run (tRets := tRets) params env (if c then j else j') =
      if c then Jump.run params env j else Jump.run params env j' := by
  split <;> rfl

@[simp]
theorem Env.writeMany_nil (E : ⟪Γ⟫) : E.writeMany .nil .nil = E :=
  rfl

open Lean Meta in
/-- Reduce a block's parameters `params k` in a `writeMany` to their `Dsts` literal, so
`writeMany_cons`/`writeMany_nil` apply: `params` is a function of the program, defined by cases. -/
dsimproc [mlir_instr]reduceWriteManyDsts (Env.writeMany _ _ _) := fun e => do
  let_expr Env.writeMany _ _ env ds vs := e | return .continue
  if ds.isAppOf ``Dsts.cons || ds.isAppOf ``Dsts.nil then
    return .continue
  let ds' ← withTransparency .default (whnf ds)
  unless ds'.isAppOf ``Dsts.cons || ds'.isAppOf ``Dsts.nil do
    return .continue
  return .visit (mkAppN e.getAppFn (e.getAppArgs.set! 3 ds'))

@[simp]
theorem Env.writeMany_cons (E : ⟪Γ⟫) :
    E.writeMany (.cons d ds) (.cons v vs) = E[d := v].writeMany ds vs :=
  rfl

end ControlFlow

end

end MLIR

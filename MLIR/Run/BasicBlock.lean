module

public import MLIR.Semantics.Func

namespace MLIR

public section

/-- Run from `E'` instead of the equal `E`: `run_from` matches `E` to a lemma's env. -/
theorem Func.runFrom_of_env_eq {f : Func} {E E' : ⟪f.Γ⟫} {k s K} (he : E' = E)
    (h : f.runFrom E' k s = K) : f.runFrom E k s = K :=
  he ▸ h

/-- `runFrom_of_env_eq` under a bind: a framed function's run, before its frame erase. -/
theorem Func.runFrom_bind_of_env_eq {f : Func} {E E' : ⟪f.Γ⟫} {k s}
    {g : Vals f.tRets × GlobalState → PoisonOr β} {K} (he : E' = E)
    (h : (f.runFrom E' k s >>= g) = K) : (f.runFrom E k s >>= g) = K :=
  he ▸ h

/-- A bare run by a lemma stated under a bind (a framed function's), the bind `pure`. -/
theorem Func.runFrom_of_bind_pure {f : Func} {E : ⟪f.Γ⟫} {k s K}
    (h : (f.runFrom E k s >>= pure) = K) : f.runFrom E k s = K := by
  rwa [bind_pure] at h

/-- A body fact `l.drop n = x :: xs` puts `n` inside `l`. -/
theorem List.lt_length_of_drop_eq_cons {l : List α} (h : l.drop n = x :: xs) : n < l.length := by
  rcases Nat.lt_or_ge n l.length with h' | h'
  · exact h'
  · rw [List.drop_eq_nil_of_le h'] at h
    cases h

/-- A body fact `l.drop n = x :: xs`: the instruction at `n` is `x`. -/
theorem List.getElem_of_drop_eq_cons {l : List α} (h : l.drop n = x :: xs) :
    l[n]'(List.lt_length_of_drop_eq_cons h) = x := by
  rw [List.drop_eq_getElem_cons (List.lt_length_of_drop_eq_cons h)] at h
  injection h

/-- A `Nodup` list's elements at positions `i < j` differ. -/
theorem List.Nodup.getElem_ne {l : List α} (h : l.Nodup) (hij : i < j) (hj : j < l.length) :
    l[i] ≠ l[j] :=
  List.pairwise_iff_getElem.1 h i j (by omega) hj hij

/-- A body fact `l.drop n = x :: xs`, one instruction on. -/
theorem List.drop_succ_of_drop_eq_cons {l : List α} (h : l.drop n = x :: xs) :
    l.drop (n + 1) = xs := by
  rw [List.drop_eq_getElem_cons (List.lt_length_of_drop_eq_cons h)] at h
  injection h

/-- A body fact `l.drop n = xs ++ ys`, past `xs`. -/
theorem List.drop_add_of_drop_eq_append {l : List α} (h : l.drop n = xs ++ ys) :
    l.drop (n + xs.length) = ys := by rw [← List.drop_drop, h, List.drop_left]

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

/-- At the end of a body, by a body fact `block.body.drop pos = []`. -/
theorem BasicBlock.runBodyFrom_done_of_drop {block : BasicBlock Γ tRets bp} {env : ⟪Γ⟫}
    (h : block.body.drop pos = []) : block.runBodyFrom env pos = pure env := by
  rw [runBodyFrom, h, List.foldlM_nil]

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
  | Ty.vec _ _ =>
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
  let_expr Env.writeMany _ _ _ ds _ := e | return .continue
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

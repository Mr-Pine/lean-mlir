module

public meta import MLIR.Run.Tactic.Step.Alloca
public meta import MLIR.Semantics.GlobalInitializer
public import MLIR.Run.Memory

namespace MLIR

open Lean Elab Tactic Meta

public meta section

/-- `step_impure` for an `addressof` of a global `g`, from `hv : ∀ s, g.value s = .value (x, s)` or
from `g` itself: a fresh block holding `x`'s bits, defined but where `x` is poison and in padding.
As with `step_alloca`, the new block is named `x` and kept apart from the pointers with memory
facts. -/
syntax (name := stepAddressof) "step_addressof" term:max (stepNames)? (stepConsuming)? : tactic

/-- The value `g`'s initializer computes, read off its block (each register its instruction's
`compute` of the registers it reads), with `∀ s, g.value s = .value (x, s)` for the kernel to check
by running the block: the instructions are not evaluated. -/
def globalValue (g : Expr) : MetaM (Expr × Expr) := do
  let some c := g.getAppFn.constName? | throwError "`step_addressof`: {g} is not a global"
  let some entry := (← getEnv).find? (c ++ `entry) |>.bind (·.value?)
    | throwError "`step_addressof`: no initializer block `{c ++ `entry}`"
  -- a long block's instructions are shared by `have`s
  let entry ← zetaReduce entry
  let_expr BasicBlock.mk _ _ _ _ body exit := entry
    | throwError "`step_addressof`: {c ++ `entry} is no block literal"
  let index (i : Expr) : MetaM Nat := do
    let some k ← Tactic.kernelNat? (mkApp2 (mkConst ``Fin.val) (← inferType i).appArg! i)
      | throwError "`step_addressof`: register {i} is no literal"
    return k
  let regIndex (r : Expr) : MetaM Nat := do
    let_expr Reg.val _ _ i _ := r | throwError "`step_addressof`: {r} is no value register"
    index i
  let dstIndex (d : Expr) : MetaM Nat := do
    let_expr Dst.mk _ _ i _ := d | throwError "`step_addressof`: {d} is no register"
    index i
  let mut vals : Std.HashMap Nat Expr := {}
  let mut instrs := body
  while instrs.isAppOfArity ``List.cons 3 do
    let i := instrs.getArg! 1
    instrs := instrs.getArg! 2
    let read (r : Expr) : MetaM Expr := do
      let some v := vals[← regIndex r]? | throwError "`step_addressof`: {r} read before written"
      return v
    match_expr i with
    | Instr.const _ τ v d => vals := vals.insert (← dstIndex d) (← mkAppOptM ``Ty.wrap #[τ, v])
    | Instr.poison _ τ d => vals := vals.insert (← dstIndex d) (mkApp (mkConst ``Ty.poisoned) τ)
    | Instr.unop _ t₁ t op d a =>
      vals := vals.insert (← dstIndex d) (mkApp4 (mkConst ``UnOp.compute) t₁ t op (← read a))
    | Instr.binop _ t₁ t₂ t op d a b =>
      vals :=
        vals.insert (← dstIndex d)
          (mkApp6 (mkConst ``BinOp.compute) t₁ t₂ t op (← read a) (← read b))
    | _ => throwError "`step_addressof`: an initializer instruction{indentExpr i}"
  let_expr Exit.ret _ _ _ _ rs := exit | throwError "`step_addressof`: the initializer's exit"
  let_expr Regs.cons _ _ _ r _ := rs | throwError "`step_addressof`: the initializer's exit"
  let some x := vals[← regIndex r]? | throwError "`step_addressof`: the returned register"
  let hv ←
    withLocalDeclD `s (mkConst ``GlobalState) fun s => do
      let lhs ← mkAppM ``GlobalInitializer.value #[g, s]
      let rhs ← mkAppM ``PoisonOr.value #[← mkAppM ``Prod.mk #[x, s]]
      mkLambdaFVars #[s] (← Tactic.kernelRfl lhs rhs)
  return (x, hv)

/-- Close `goal` by the lemma `lem`, its arguments `args` where given, the others by unifying its
conclusion with the goal. -/
def applyWith (goal : MVarId) (lem : Name) (args : Array (Option Expr)) : MetaM Unit := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType c)
  for (m, a?) in ms.zip args do
    if let some a := a? then
      unless ← isDefEq m a do
        throwError "`addressof_value`: {lem}'s argument{indentExpr a}"
  unless ← isDefEq ty (← goal.getType) do
    throwError "`addressof_value`: {lem} does not close{indentExpr (← goal.getType)}"
  goal.assign (← instantiateMVars (mkAppN c ms))

/-- Close the run goal of `addressof` of a global `g`, from `hv : ∀ s, g.value s = .value (x, s)`
or `g` itself (`globalValue`): with `run_addressof_wrap` for `x = Ty.wrap r` of a type without
pointers and padding, else with `run_addressof_def`, `x`'s bits and definedness literals the kernel
evaluates (`Ty.flattenNat`), no `exponentiation.threshold` and no recursion limit in the way. -/
elab "addressof_value" hv:term:max : tactic =>
  withMainContext do
    let hv ← elabTerm hv none
    let (hv, ty) ←
      if (← whnfR (← inferType hv)).isConstOf ``GlobalInitializer then
        let (_, h) ← globalValue hv
        pure (h, ← inferType h)
      else
        pure (hv, ← inferType hv)
    let some (v, x) ←
        forallTelescope ty fun _ body => do
          let some v := body.find? (·.isAppOfArity ``GlobalInitializer.value 1) | return none
          -- `.value (x, s)`
          let some (_, _, rhs) := body.eq? | return none
          unless rhs.isAppOfArity ``PoisonOr.value 2 do
            return none
          return some (v, rhs.appArg!.appFn!.appArg!)
      | throwError "`addressof_value`: {hv} is not about a global's `value`:{indentExpr ty}"
    -- the type spelled out, so the stored bits are about it rather than `g.t`
    let t ← reduce (← mkAppM ``GlobalInitializer.t #[v.appArg!])
    -- the width and byte count as literals, so the state's `storeAt` and the bits agree on them
    let some w ← Tactic.kernelNat? (mkApp (mkConst ``Ty.width) t)
      | throwError "`addressof_value`: the width of{indentExpr t}\nis not a literal"
    let n := (w + 7) / 8
    let (wE, nE) := (mkNatLit w, mkNatLit n)
    let goal ← getMainGoal
    -- the state, from `hv`'s type at the goal's: `Instr.run`'s, unfolded
    let s ← mkFreshExprMVar (mkConst ``GlobalState)
    let hvs := mkApp (← instantiateMVars hv) s
    let hw ← Tactic.kernelRfl (mkApp (mkConst ``Ty.width) t) wE
    let hn ← Tactic.kernelRfl (← mkAppM ``HDiv.hDiv #[← mkAppM ``HAdd.hAdd #[wE, mkNatLit 7],
      mkNatLit 8]) nE
    let isFalse (p : Expr) : MetaM (Option Expr) := do
      Tactic.kernelDecide? (← mkEq p (mkConst ``Bool.false))
    -- the plain value of a type without pointers and padding: all its bits, defined
    if x.isAppOfArity ``Ty.wrap 2 then
      if let some hp ← isFalse (mkApp (mkConst ``Ty.hasPtr) t) then
        if let some hpad ← isFalse (mkApp (mkConst ``Ty.hasPadding) t) then
          applyWith goal ``run_addressof_wrap
            #[none, none, s, t, v, x.appArg!, none, wE, nE, hvs, hp, hpad, hw, hn]
          return
    -- the bits and their definedness, as literals the kernel evaluates
    let lit (f : Name) : MetaM (Expr × Expr) := do
      let e := mkApp2 (mkConst ``Ty.flattenNat) t (mkApp2 (mkConst f) t x)
      let some k ← Tactic.kernelNat? e
        | throwError "`addressof_value`: the initializer's bits are no literal"
      return (mkNatLit k, ← Tactic.kernelRfl e (mkNatLit k))
    let (b, hb) ← lit ``Ty.valueOrZero
    let (d, hd) ← lit ``Ty.definedness
    let hx ← mkAppOptM ``Ty.flattenDef_eq_ofNat #[t, x, wE, b, d, hw, hb, hd]
    let leaves := mkApp3 (mkConst ``Ty.ptrLeaves) t (mkNatLit 0) x
    unless (← Tactic.kernelWhnf leaves).isAppOf ``List.nil do
      throwError "`addressof_value`: a global holding pointers{indentExpr x}"
    let hl ← Tactic.kernelRfl leaves (← mkAppOptM ``List.nil #[← mkAppM ``Prod #[mkConst ``Nat,
      mkConst ``Pointer]])
    let bitsOf (k : Expr) := mkApp2 (mkConst ``BitVec.ofNat) wE k
    applyWith goal ``run_addressof_def
      #[none, none, s, t, v, x, none, wE, nE, bitsOf b, bitsOf d, hvs, hl, hw, hx, hn]

@[tactic stepAddressof]
def evalStepAddressof : Tactic := fun stx => do
  addAllocaFreshness "step_addressof"
  runStep (StepArgs.parse mkNullNode stx[2] stx[3] mkNullNode (named := true))
      (← `(tacticSeq| addressof_value $(⟨stx[1]⟩)))
  nameAllocaSlot

end

end MLIR

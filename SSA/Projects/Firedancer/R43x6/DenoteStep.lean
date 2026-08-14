/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.SLLVM.Tactic

/-!
# Sharing-preserving symbolic execution of pure `Com`s

`simp_peephole` denotes a program by substituting every SSA value's defining
expression into all of its use sites. That turns the SSA DAG into a tree: for
programs that use intermediate values more than once (like
`fd_r43x6_mul_fast`, where the `t`-vectors, `zl` and `zb` all have fan-out
2-3), the fully inlined term grows multiplicatively and becomes intractable.

This file provides `denote_step_all`, which instead peels one let-binding at a
time: each instruction's value is `generalize`d to a fresh opaque variable
before the next instruction is processed, so a use of an intermediate value is
just a variable and sharing is preserved. The per-instruction definitions are
recorded as hypotheses `hv0 : v0 = …`, `hv1 : v1 = …`, …, which can then be
processed *individually* (each one is small), and used via `simp only [*]` to
expand uses of the `v<i>` on demand.
-/

namespace Firedancer.StepTactic
-- NOTE: `Expr`/`Com` live in the root namespace, so our helper defs do too;
-- this namespace only scopes the section variables.
end Firedancer.StepTactic

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [Monad d.m] [LawfulMonad d.m]

/-- `Expr.denoteOp`, at the `HVector` type it definitionally has for a pure
expression. Having this as its own definition gives the stepping tactic a
stable head symbol to generalize, with a type that type-class resolution is
happy with. -/
def Expr.denoteOpPure {Γ : Ctxt d.Ty} {ts : List d.Ty}
    (e : Expr d Γ .pure ts) (V : Γ.Valuation) : HVector TyDenote.toType ts :=
  e.denoteOp V

/-- The head value of a pure single-result expression. -/
def Expr.denoteOp1 {Γ : Ctxt d.Ty} {t : d.Ty}
    (e : Expr d Γ .pure [t]) (V : Γ.Valuation) : TyDenote.toType t :=
  (e.denoteOpPure V).head

theorem Com.denote_var_pure {Γ : Ctxt d.Ty} {ts' ts : List d.Ty}
    (e : Expr d Γ .pure ts') (body : Com d e.outContext .pure ts)
    (V : Γ.Valuation) :
    (Com.var e body).denote V
      = body.denote (e.denoteOpPure V ++ V) := by
  rcases e with ⟨op, rfl, eff_le, args, regArgs⟩
  simp only [Com.denote_var, Expr.denote, Expr.denoteOpPure, Expr.denoteOp]
  rfl

/-- As `Com.denote_var_pure`, but for the (common) single-result case, pushing
the value into the valuation as a `Valuation.cons`. -/
theorem Com.denote_var_pure_single {Γ : Ctxt d.Ty} {t : d.Ty} {ts : List d.Ty}
    (e : Expr d Γ .pure [t]) (body : Com d e.outContext .pure ts)
    (V : Γ.Valuation) :
    (Com.var e body).denote V
      = body.denote (e.denoteOp1 V ::ᵥ V) := by
  rw [Com.denote_var_pure]
  congr 1
  show e.denoteOpPure V ++ V = (e.denoteOpPure V).head ::ᵥ V
  generalize e.denoteOpPure V = w
  cases w
  case cons a as =>
    cases as
    show (Ctxt.Valuation.ofHVector (a ::ₕ .nil)) ++ V = a ::ᵥ V
    simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
      Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]

open Lean Meta Elab Tactic in
/-- `denote_step_all v` symbolically executes a pure, single-result-per-op
`Com` denotation: as long as the goal has the shape
`(Com.var e body).denote V = rhs`, it introduces a fresh variable `v<i>` with
defining hypothesis `hv<i> : v<i> = e.denoteOp1 V` and changes the goal to
`body.denote (v<i> ::ᵥ V) = rhs` (via `Com.denote_var_pure_single`). Sharing
between use sites is preserved — every use of an intermediate value is just a
variable — and each `hv<i>` can be simplified in isolation.

This is pure term surgery (no `rw`), so each step is cheap even when the
remaining program is large. -/
elab "denote_step_all" base:ident : tactic => do
  let baseName := base.getId
  let mut i := 0
  for _ in [0:1000] do
    let goal ← getMainGoal
    let step? ← goal.withContext do
      let tgt ← whnfR (← instantiateMVars (← goal.getType))
      let some (_, lhs, rhs) := tgt.eq? | return none
      let lhs ← whnfR lhs
      unless lhs.isAppOf ``Com.denote do return none
      let lhsArgs := lhs.getAppArgs
      unless lhsArgs.size ≥ 2 do return none
      let com ← whnfR lhsArgs[lhsArgs.size - 2]!
      let V := lhsArgs[lhsArgs.size - 1]!
      unless com.isAppOf ``Com.var do return none
      let comArgs := com.getAppArgs
      unless comArgs.size ≥ 2 do return none
      let e := comArgs[comArgs.size - 2]!
      let body := comArgs[comArgs.size - 1]!
      -- stepEq : (Com.var e body).denote V = body.denote (e.denoteOp1 V ::ᵥ V)
      let stepEq ← mkAppM ``Com.denote_var_pure_single #[e, body, V]
      let tVal ← mkAppM ``Expr.denoteOp1 #[e, V]
      let vName := baseName.appendAfter (toString i)
      let hName := Name.mkSimple ("h" ++ vName.toString)
      -- newType : ∀ v, v = e.denoteOp1 V → body.denote (v ::ᵥ V) = rhs
      -- (oriented `v = def` so `simp only [*]` expands uses of `v` on demand)
      let newType ← withLocalDeclD vName (← inferType tVal) fun v => do
        let defEq ← mkEq v tVal
        let consV ← mkAppM ``Ctxt.Valuation.cons #[v, V]
        let newLhs ← mkAppM ``Com.denote #[body, consV]
        let concl ← mkEq newLhs rhs
        withLocalDeclD hName defEq fun h =>
          mkForallFVars #[v, h] concl
      let newGoal ← mkFreshExprSyntheticOpaqueMVar newType
      -- oldGoal := stepEq.trans (newGoal (e.denoteOp1 V) rfl)
      let rflPrf ← mkEqRefl tVal
      let contPrf := mkApp2 newGoal tVal rflPrf
      goal.assign (← mkEqTrans stepEq contPrf)
      let (_, goal2) ← newGoal.mvarId!.introN 2 [vName, hName]
      return some goal2
    let some goal2 := step? | break
    replaceMainGoal [goal2]
    i := i + 1

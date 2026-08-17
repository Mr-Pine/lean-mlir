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
/-- One step of `denote_step_all`: if the main goal has the shape
`(Com.var e body).denote V = rhs`, introduce `v<i> : _` together with
`hv<i> : v<i> = e.denoteOp1 V` and return the goal
`body.denote (v<i> ::ᵥ V) = rhs`. Returns `none` if the goal is not of that
shape (i.e. the program is exhausted). -/
private def denoteStep1 (goal : MVarId) (baseName : Name) (i : Nat) :
    MetaM (Option MVarId) :=
  goal.withContext do
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

open Lean Meta in
/-- The length of a valuation's `Ctxt.Valuation.cons` spine. Only the
syntactic head is inspected, so a base valuation built with `singleton` /
`ofPair` / an opaque variable contributes `0` — matching MLIR, where the block
arguments are `%arg0…` and do not participate in the `%0, %1, …` numbering. -/
private partial def valuationDepth (V : Expr) : Nat :=
  if V.isAppOf ``Ctxt.Valuation.cons then
    let args := V.getAppArgs
    if args.size ≥ 1 then valuationDepth args[args.size - 1]! + 1 else 0
  else 0

open Lean Meta Elab Tactic in
/-- The number of instructions already consumed, i.e. the index to give the
next `v<i>`.

This is read off the *goal*, not off hypothesis names: every step wraps the
valuation in one more `Ctxt.Valuation.cons`, and that spine is part of the
denotation being rewritten, so it survives anything done to the context —
renaming, `clear`ing the `hv<i>`, or `subst`ing a `v<i>` away. The index
therefore always agrees with the `%i` of the MLIR program. -/
private def nextStepIndex (goal : MVarId) : MetaM Nat :=
  goal.withContext do
    let tgt ← whnfR (← instantiateMVars (← goal.getType))
    let some (_, lhs, _) := tgt.eq? | return 0
    let lhs ← whnfR lhs
    unless lhs.isAppOf ``Com.denote do return 0
    let args := lhs.getAppArgs
    unless args.size ≥ 1 do return 0
    return valuationDepth args[args.size - 1]!

open Lean Meta Elab Tactic in
/-- `denote_step_all v` symbolically executes a pure, single-result-per-op
`Com` denotation: as long as the goal has the shape
`(Com.var e body).denote V = rhs`, it introduces a fresh variable `v<i>` with
defining hypothesis `hv<i> : v<i> = e.denoteOp1 V` and changes the goal to
`body.denote (v<i> ::ᵥ V) = rhs` (via `Com.denote_var_pure_single`). Sharing
between use sites is preserved — every use of an intermediate value is just a
variable — and each `hv<i>` can be simplified in isolation.

This is pure term surgery (no `rw`), so each step is cheap even when the
remaining program is large.

`denote_step_all v n` runs *to* instruction `%n` of the MLIR program, like a
debugger's "run to line": it stops once `v<n>` exists, leaving `v0 … v<n>` in
context and the goal positioned at `%(n+1)`. The argument is an absolute
instruction number, not a number of steps — `denote_step_all v 31` always
means "up to and including `%31`", however many steps that takes from here.

Numbering is per-program, so it composes: `denote_step_all v 3` followed by
`denote_step_all v 5` introduces `v0 … v3` and then `v4 v5`, exactly as a
single `denote_step_all v 5` would. The continuation point is `nextStepIndex`,
which reads the instruction count off the goal, so `v<i>` names the program's
`%i` no matter what happened to the context in between — the `hv<i>` may be
`clear`ed, the `v<i>` `subst`ed away or renamed. -/
elab "denote_step_all" base:ident target:(num)? : tactic => do
  let baseName := base.getId
  let start ← nextStepIndex (← getMainGoal)
  match target with
  | none =>
    let mut i := start
    for _ in [0:1000] do
      let some goal2 ← denoteStep1 (← getMainGoal) baseName i | break
      replaceMainGoal [goal2]
      i := i + 1
  | some n =>
    let target := n.getNat
    if start > target then
      throwError "denote_step_all: already positioned at %{start}, which is \
        past the requested %{target}"
    for i in [start:target + 1] do
      let some goal2 ← denoteStep1 (← getMainGoal) baseName i
        | throwError "denote_step_all: the program has no instruction %{i}, \
            so it cannot be stepped to %{target}"
      replaceMainGoal [goal2]

/-! ### Working with a range of stepped instructions

`denote_step_all` leaves one `hv<i>` per instruction, which is what keeps each
of them small, but it means referring to a stretch of the program spells out
every name. The two tactics below take an inclusive index range instead.
-/

open Lean Meta Elab Tactic in
/-- The hypotheses `h<base><lo> … h<base><hi>` that actually exist in the main
goal's context, ascending. Indices with no hypothesis are skipped rather than
being an error, so a range may freely span `v<i>`s that have been `subst`ed
away or whose `hv<i>` has been `clear`ed. -/
private def denoteHyps (base : Name) (lo hi : Nat) : TacticM (Array Ident) := do
  (← getMainGoal).withContext do
    let lctx ← getLCtx
    let mut hyps : Array Ident := #[]
    for i in [lo:hi + 1] do
      let n := Name.mkSimple ("h" ++ base.toString ++ toString i)
      if (lctx.findFromUserName? n).isSome then
        hyps := hyps.push (mkIdent n)
    if hyps.isEmpty then
      throwError "no `h{base}<i>` hypothesis with {lo} ≤ i ≤ {hi}"
    return hyps

open Lean Elab Tactic in
/-- `denote_eval v 4 27` evaluates the stepping hypotheses `hv4 … hv27` in
place, turning each `hv<i> : v<i> = (Expr.mk …).denoteOp1 V` into the dialect
value it denotes, e.g. `hv13 : v13 = LLVM.Ty.insertelement v11 v10 v12`.

Each hypothesis is evaluated *on its own*, which is the cheap direction:
inlining a chain of instructions first and evaluating the result afterwards
does not scale. -/
elab "denote_eval " base:ident lo:num hi:num : tactic => do
  let hyps ← denoteHyps base.getId lo.getNat hi.getNat
  evalTactic (← `(tactic| simp only [Expr.denoteOp1, Expr.denoteOpPure] at $hyps*))
  evalTactic (← `(tactic| simp_peephole at $hyps*))
  evalTactic (← `(tactic| simp only [HVector.head] at $hyps*))

open Lean Elab Tactic in
/-- `denote_expand v 4 27` rewrites the goal with `hv27, hv26, …, hv4` —
descending, so a chain collapses in one pass from its last instruction down to
its inputs. The range is written ascending, as for `denote_eval`; run that
first, or the goal fills up with unevaluated `denoteOp1`s. -/
elab "denote_expand " base:ident lo:num hi:num : tactic => do
  let hyps := (← denoteHyps base.getId lo.getNat hi.getNat).reverse
  evalTactic (← `(tactic| simp only [$[$hyps:ident],*]))

open Lean Meta Elab Tactic in
/-- `denote_clear v 4 27` retires `hv4 … hv27` and `v4 … v27`, for stretches of
the program that have been dealt with and are only making the context long.

Each is `clear`ed if possible. A `v<i>` usually is not: until it is `subst`ed
away it still occurs in the goal's valuation spine, which is a real dependency.
Those are **hidden** instead — marked as implementation details, which the goal
display filters out. That changes nothing about the goal, so the spine is
untouched and `denote_step_all` numbering is unaffected.

Indices with nothing in the context are skipped, as for `denote_eval`; an
entirely empty range is an error.

A hidden hypothesis is still in scope and can still be used by name
(`exact hv11` works). What it is invisible to is automation that scans the
context — `simp at *`, `assumption`, `omega`. That is harmless for a `v<i>`,
which carries no information once its `hv<i>` is gone. -/
elab "denote_clear " base:ident lo:num hi:num : tactic => do
  let baseName := base.getId
  let lo := lo.getNat
  let hi := hi.getNat
  let goal ← getMainGoal
  let fvars ← goal.withContext do
    let lctx ← getLCtx
    let mut fvars : Array FVarId := #[]
    -- `hv<i>` mentions `v<i>`, so it has to be cleared first.
    for name in [("h" ++ baseName.toString), baseName.toString] do
      for i in [lo:hi + 1] do
        if let some d := lctx.findFromUserName? (Name.mkSimple (name ++ toString i)) then
          fvars := fvars.push d.fvarId
    return fvars
  if fvars.isEmpty then
    throwError "no `{baseName}<i>` or `h{baseName}<i>` hypothesis with \
      {lo} ≤ i ≤ {hi}"
  -- NOTE: not `tryClearMany`, which iterates its argument in *reverse* and so
  -- would try each `v<i>` while its `hv<i>` still depends on it, silently
  -- leaving every value behind.
  let mut goal := goal
  for fvar in fvars do
    goal ← goal.tryClear fvar
  -- Whatever survived the clear is depended upon; hide it instead.
  let survivors ← goal.withContext do
    let lctx ← getLCtx
    return fvars.filter fun f => (lctx.find? f).isSome
  if survivors.isEmpty then
    replaceMainGoal [goal]
  else
    goal.withContext do
      let mut lctx ← getLCtx
      for f in survivors do
        lctx := lctx.setKind f .implDetail
      let newGoal ← mkFreshExprMVarAt lctx (← getLocalInstances) (← goal.getType)
                      .syntheticOpaque (← goal.getTag)
      goal.assign newGoal
      replaceMainGoal [newGoal.mvarId!]

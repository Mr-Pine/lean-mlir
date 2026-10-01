module

public import MLIR.Semantics.Func
public import MLIR.Run.Vector
public import MLIR.Run.Tactic.Parse
public import MLIR.Run.Tactic.Memory
public import MLIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic

namespace MLIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealEnv

def sealEnvAt (env : Expr) : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    if env.isFVar then
      return
    -- the chain's root: a jump writes several parameters
    let mut E := (← getEnvWrite env).base
    while E.isAppOfArity ``Env.write 5 do
      E := E.getArg! 2
    -- without `hE`, `E` is a root (a loop's env, or a continuation's): it stays
    let hE? ← findEqWithLhs? E m!"of the form `{E} = _`"
    let hEargs? ←
      findEqWithLhs? (← mkAppM ``Env.args #[E]) m!"of the form `{(← mkAppM ``Env.args #[E])} = _"
    let abstractWrite := Expr.lam `e (← inferType E) (← withReducible <| kabstract env E) .default
    let (E₀chain, hEpf) ←
      match hE? with
      | some hE =>
        do
          let some (_, _, c) :=
            (← instantiateMVars (← hE.getType)).eq? | throwError "expected an equation"
          pure (c, ← mkCongrArg abstractWrite (mkFVar hE))
      | none =>
        pure (E, ← mkEqRefl env)
    let stmtEq := (mkEq · (abstractWrite.beta #[E₀chain]))
    let mut facts := #[⟨`hE, stmtEq, hEpf⟩]
    if let some hEargs := hEargs? then
      let some (_, _, args) :=
        (← instantiateMVars (← hEargs.getType)).eq? | throwError "expected an equation"
      let stmtArgs (e) : MetaM _ := do
        mkEq (← mkAppM ``Env.args #[e]) args
      facts := facts.push ⟨`hArgs, stmtArgs, mkExpectedPropHint (mkFVar hEargs) (← stmtArgs env)⟩
    let (_, g) ←
      g.withContext do
          generalizeOpaque g (hyps := #[]) env `E facts
    let mut g := g
    if let some hEargs := hEargs? then
      g ← g.clear hEargs
    if let some hE := hE? then
      g ← g.clear hE
      g ← g.clear E.fvarId!
    replaceMainGoal [g]

def sealEnv : TacticM Unit := do
  let (_, goal) ← getGoalType
  let runBodyFrom ← getRunBodyFrom goal
  sealEnvAt runBodyFrom.env

elab "seal_env" : tactic => sealEnv

end SealEnv

section ResolveReads

/-- Reduce `args i` access by unfolding -/
def reduceArgsApp : Simp.DSimproc := fun app => do
  let index := app.appArg!
  let some finBound := (← whnf (← inferType index)).app1? ``Fin | return .continue
  let some literal ← finNLit? index | return .continue
  let inBounds ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit literal, finBound])
  let litIndex ← mkAppOptM ``Fin.mk #[finBound, mkNatLit literal, inBounds]
  let some unfolded ← withDefault (unfoldDefinition? (mkApp app.appFn! litIndex)) | return .continue
  let reduced ← whnfCore unfolded
  return if reduced == app then .continue else .done reduced

/-- For a fact `h : _.args = argsFn`, this keys `reduceArgsApp` on applications of `argsFn` -/
def argsSimprocs (fact : FVarId) : MetaM Simp.Simprocs := do
  let simprocs ← Simp.getSimprocs
  let some (_, _, argsFn) := (← instantiateMVars (← fact.getType)).eq? | return simprocs -- Find
  let .forallE _ indexType _ _ := ← whnf (← inferType argsFn) | return simprocs
  let keys ← DiscrTree.mkPath (mkApp argsFn (← mkFreshExprMVar indexType))
  return simprocs.addCore keys ``reduceArgsApp false (.inr reduceArgsApp)

def decideDischarge : Simp.Discharge := fun prop => do
  if let .some inst← trySynthInstance (← mkAppM ``Decidable #[prop]) then
    let value ← withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) prop inst)
    if value.isConstOf ``Bool.true then
      return (← mkDecideProof prop)
  -- abstract registers (a pattern lemma's): a local `h : prop`, or `h : j ≠ i` for `i ≠ j`
  let symm? ←
    match prop.ne? with
    | some (_, a, b) =>
      some <$> mkAppM ``Ne #[b, a]
    | none =>
      pure none
  -- `a ≠ b` (maybe an `autoParam`), or simp's `¬ a = b`
  let ne := (← instantiateMVars prop).cleanupAnnotations
  let sides? :=
    match ne.ne? with
    | some (_, a, b) => some (a, b)
    | none => ne.not?.bind (·.eq?) |>.map fun (_, a, b) => (a, b)
  for d in ← getLCtx do
    if d.isImplementationDetail then
      continue
    if ← withReducible (isDefEq d.type prop) then
      return some d.toExpr
    if let some symm := symm? then
      if ← withReducible (isDefEq d.type symm) then
        return some (← mkAppM ``Ne.symm #[d.toExpr])
    if let some (a, b) := sides? then
      if let some h← nodupNe? d.toExpr (← instantiateMVars d.type) a b then
        return some (← mkExpectedTypeHint h prop)
  return none

/-- Register `i` of `e`, an env without a chain fact, from a local `h : e.read (.val i _) = v`: a
read at a block lemma's entry env. `lhs` is the read being resolved, `e.read` of `i` up to the
skipped writes. -/
def readFact? (e : Expr) (i : Nat) (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then
      continue
    let some (_, l, v) := (← instantiateMVars d.type).eq? | continue
    let_expr Env.read _ _ e' r := l | continue
    unless e' == e do
      continue
    let_expr Reg.val _ _ rj _ := r | continue
    unless (← finNLit? rj) == some i do
      continue
    return some (v, mkExpectedPropHint d.toExpr (← mkEq lhs v))
  return none

/-- `env.read reg` through `env`'s write chains: the value last written to `reg`, and the proof.
Each run of writes is one definitional step (the kernel decides the index comparisons), each
local's `hE` one rewrite. Unlike `simp`, it never walks the written values. -/
partial def walkRead (env reg : Expr) : MetaM (Option (Expr × Expr)) := do
  let_expr Reg.val _ _ ri _ := reg | return none
  let some i ← finNLit? ri | return none
  let lhs ← mkAppM ``Env.read #[env, reg]
  -- down this run of writes: the value, or the run's base
  let mut e := env
  while e.isAppOfArity ``Env.write 5 do
    let some j ← dstIndex? (e.getArg! 3) | return none
    if i == j then
      let v := e.getArg! 4
      return some (v, mkExpectedPropHint (← mkEqRefl v) (← mkEq lhs v))
    e := e.getArg! 2
  unless e.isFVar do
    return none
  let some hE ← findEqWithLhs? e m!"" | readFact? e i lhs
  let some (_, _, chain) := (← instantiateMVars (← hE.getType)).eq? | return none
  let some (v, pf) ← walkRead chain reg | return none
  let baseRead ← mkAppM ``Env.read #[e, reg]
  let readOf ←
    withLocalDeclD `x (← inferType e) fun x => do
        mkLambdaFVars #[x] (← mkAppM ``Env.read #[x, reg])
  -- `env.read reg = e.read reg` (the run skipped), `= chain.read reg` (`hE`), `= v`
  let skip := mkExpectedPropHint (← mkEqRefl baseRead) (← mkEq lhs baseRead)
  return some (v, ← mkEqTrans skip (← mkEqTrans (← mkCongrArg readOf (.fvar hE)) pf))

/-- `walkRead` as a simproc: a register read, resolved without walking the written values. -/
simproc_decl readThroughWrites (Env.read _ _) := fun e => do
  let_expr Env.read _ _ env reg := e | return .continue
  let some (v, pf) ← walkRead env reg | return .continue
  return .visit { expr := v, proof? := pf }

/-- One `mlir_env` pass over `e`, with `facts` as extra rewrite rules and `readThroughStore`.
The first fact is the one `argsSimprocs` reduces `Env.args` with. -/
def simpPass (only : Bool) (simpArgs : Syntax) (e : Expr) (facts : Array FVarId) :
    TacticM Simp.Result := do
  let some ext ← getSimpExtension? `mlir_env | throwError "no `mlir_env` simp set"
  let mut thms ←
    if only then
      pure {}
    else
      getSimpTheorems
  for fact in facts do
    thms ← thms.add (.fvar fact) #[] (mkFVar fact)
    -- an argument read's fact also in `read_arg`'s form, which the args pass rewrites reads to
    if let some (_, l, v) := (← instantiateMVars (← fact.getType)).eq? then
      if l.isAppOfArity ``Env.read 4 && (l.getArg! 3).isAppOf ``Reg.arg then
        let (_, _, ty) ←
          forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels ``Env.read_arg))
        if let some (_, ll, rr) := ty.eq? then
          if ← isDefEq ll l then
            let pf := mkExpectedPropHint (mkFVar fact) (← mkEq (← instantiateMVars rr) v)
            thms ← thms.add (.other `argReadFact) #[] pf
  -- operations unfold, even with `only`: the step machinery, like `mlir_env`
  let some ops ← getSimpExtension? `mlir_operation | throwError "no `mlir_operation` simp set"
  let opThms ← ops.getTheorems
  let ctx ←
    Simp.mkContext (simpTheorems := #[thms, (← ext.getTheorems), opThms]) (congrTheorems :=
        ← getSimpCongrTheorems)
  let procs :=
    #[←
        if h : 0 < facts.size then
          argsSimprocs facts[0]
        else
          Simp.getSimprocs,
      ← ({} : Simp.Simprocs).add ``readThroughWrites (post := false), ← memSimprocs,
      ← ({} : Simp.Simprocs).add ``readThroughStore (post := true),
      ← ({} : Simp.Simprocs).add ``gepValue (post := true)]
  let elaborated ← elabSimpArgs simpArgs ctx procs (eraseLocal := false) (kind := .simp)
  return (←
        simp e elaborated.ctx (simprocs := elaborated.simprocs) (discharge? := decideDischarge)).1

/-- The state equations `S = …` in context -/
def stateFacts : MetaM (Array FVarId) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let some (_, l, _) := (← instantiateMVars d.type).eq? | return acc
      return if l.isFVar && (← inferType l).isConstOf ``GlobalState then acc.push d.fvarId else acc

/-- The equations `x = _` of the locals in `e`: the state `S = …` and the step values `v = …`
it reads; with `keepNamed`, not those of values named with `with`. -/
private def valueStateFacts (e : Expr) (keepNamed := false) : MetaM (Array FVarId) := do
  let xs := (collectFVars {} e).fvarSet
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let some (_, .fvar x, _) := (← instantiateMVars d.type).eq? | return acc
      unless xs.contains x do
        return acc
      -- the state's equation always; a value's only if its name is generated
      if
          keepNamed && !(← inferType (.fvar x)).isConstOf ``GlobalState &&
            !isAutoValueName (← x.getUserName) then
        return acc
      return acc.push d.fvarId

/-- The local facts `E.read r = v` (a pattern lemma's inputs): read resolution goes through them as
through `hE`. -/
def readFacts : MetaM (Array FVarId) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let some (_, l, _) := (← instantiateMVars d.type).eq? | return acc
      return if l.isAppOf ``Env.read then acc.push d.fvarId else acc

/-- Resolve the reads in `e`: arguments first, against `argsFact : E.args = _`,
then values, unfolding the write chain with `chainFact : E = _`.
Unfolding first would send the argument reads past `E` down to the root env. -/
def simpValue (only : Bool) (simpArgs : Syntax) (e : Expr) (env : Expr) (expand : Bool)
    (keepNamed := false) : TacticM Simp.Result := do
  let argsFact := (← findEqWithLhs? (← mkAppM ``Env.args #[env]) m!"`{env}.args = _`").toArray
  let chainFact := (← findEqWithLhs? env m!"`{env} = _`").toArray
  let reads ← readFacts
  let args ← simpPass only simpArgs e argsFact
  let vals ← simpPass true simpArgs args.expr (chainFact ++ reads)
  let r ← args.mkEqTrans vals
  let facts ←
    if expand then
      valueStateFacts r.expr keepNamed
    else
      stateFacts
  let r ←
    if facts.isEmpty then
      pure r
    else
      r.mkEqTrans (← simpPass only simpArgs r.expr (argsFact ++ facts ++ reads))
  -- last: `#v[.value x, …]` to `Ty.wrap #v[x, …]`, once every lane is final
  let ctx ← Simp.mkContext
  let (p, _) ← simp r.expr ctx (simprocs := #[← ({} : Simp.Simprocs).add ``pullWrap (post := true)])
  r.mkEqTrans p

end ResolveReads

end

end MLIR.Tactic

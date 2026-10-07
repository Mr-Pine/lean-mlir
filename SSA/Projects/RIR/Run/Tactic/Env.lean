module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.Vector
public import SSA.Projects.RIR.Run.Tactic.Parse
public import SSA.Projects.RIR.Run.Tactic.Memory
public import SSA.Projects.RIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealEnv

/-- The root of a write chain. -/
partial def envRoot (e : Expr) : Expr :=
  if e.isAppOfArity ``Env.write 5 then envRoot (e.getArg! 2) else e

def sealEnvAt (env : Expr) : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    if env.isFVar then
      return
    -- the chain's root: a jump writes several parameters
    let E := envRoot (← getEnvWrite env).base
    -- without `hE`, `E` is a root (a loop's env, or a continuation's): it stays
    let hE? ← findLocalEq? E m!"of the form `{E} = _`"
    let hEargs? ←
      findLocalEq? (← mkAppM ``Env.args #[E]) m!"of the form `{(← mkAppM ``Env.args #[E])} = _"
    let abstractWrite := Expr.lam `e (← inferType E) (← withReducible <| kabstract env E) .default
    let (E₀chain, hEpf) ←
      match hE? with
      | some hE =>
        pure (hE.rhs, ← mkCongrArg abstractWrite hE.decl.toExpr)
      | none =>
        pure (E, ← mkEqRefl env)
    let stmtEq := (mkEq · (abstractWrite.beta #[E₀chain]))
    let mut facts := #[⟨`hE, stmtEq, hEpf⟩]
    if let some hEargs := hEargs? then
      let stmtArgs (e) : MetaM _ := do
        mkEq (← mkAppM ``Env.args #[e]) hEargs.rhs
      facts := facts.push ⟨`hArgs, stmtArgs, mkExpectedPropHint hEargs.decl.toExpr (← stmtArgs env)⟩
    let (_, g) ←
      g.withContext do
          generalizeOpaque g env `E facts
    let mut g := g
    if let some hEargs := hEargs? then
      g ← g.clear hEargs.decl.fvarId
    if let some hE := hE? then
      g ← g.clear hE.decl.fvarId
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
  if let some pf← decideProof? prop then
    return pf
  -- abstract registers (a pattern lemma's): a local `h : prop`, or `h : j ≠ i` for `i ≠ j`
  let symm? ←
    match prop.ne? with
    | some (_, a, b) =>
      some <$> mkAppM ``Ne #[b, a]
    | none =>
      pure none
  -- `a ≠ b`, or simp's `¬ a = b`
  let sides? := neSides? (← instantiateMVars prop)
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
  for (h, ty) in ← splitConjunctedFacts do
    let some (_, l, v) := (← instantiateMVars ty).eq? | continue
    let_expr Env.read _ _ e' r := l | continue
    unless e' == e do
      continue
    let_expr Reg.val _ _ rj _ := r | continue
    unless (← finNLit? rj) == some i do
      continue
    return some (v, mkExpectedPropHint h (← mkEq lhs v))
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
  let some hE ← findLocalEq? e m!"" | readFact? e i lhs
  let some (v, pf) ← walkRead hE.rhs reg | return none
  let baseRead ← mkAppM ``Env.read #[e, reg]
  let readOf ←
    withLocalDeclD `x (← inferType e) fun x => do
        mkLambdaFVars #[x] (← mkAppM ``Env.read #[x, reg])
  -- `env.read reg = e.read reg` (the run skipped), `= chain.read reg` (`hE`), `= v`
  let skip := mkExpectedPropHint (← mkEqRefl baseRead) (← mkEq lhs baseRead)
  return some (v, ← mkEqTrans skip (← mkEqTrans (← mkCongrArg readOf hE.decl.toExpr) pf))

/-- `walkRead` as a simproc: a register read, resolved without walking the written values. -/
simproc_decl readThroughWrites (Env.read _ _) := fun e => do
  let_expr Env.read _ _ env reg := e | return .continue
  let some (v, pf) ← walkRead env reg | return .continue
  return .visit { expr := v, proof? := pf }

/-- One `mlir_env` pass over `e`, with `facts` as extra rewrite rules and `readThroughStore`.
The first fact is the one `argsSimprocs` reduces `Env.args` with. -/
def simpPass (only : Bool) (simpArgs : Syntax) (e : Expr) (facts : Array FVarId) :
    TacticM Simp.Result := do
  let mut thms ←
    if only then
      pure {}
    else
      getSimpTheorems
  for fact in facts do
    thms ← thms.add (.fvar fact) #[] (mkFVar fact)
    -- an argument read's fact also in `read_arg`'s form, which the args pass rewrites reads to;
    -- a fact's conjuncts each (`E ⊨ [r := v, …]`)
    for (h, ty) in ← conjuncts (mkFVar fact) (← instantiateMVars (← fact.getType)) do
      let some (_, l, v) := ty.eq? | continue
      if l.isAppOfArity ``Env.read 4 && (l.getArg! 3).isAppOf ``Reg.arg then
        let (_, _, ty) ←
          forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels ``Env.read_arg))
        if let some (_, ll, rr) := ty.eq? then
          if ← isDefEq ll l then
            let pf := mkExpectedPropHint h (← mkEq (← instantiateMVars rr) v)
            thms ← thms.add (.other `argReadFact) #[] pf
  -- operations unfold, even with `only`: the step machinery, like `mlir_env`
  let ctx ← simpSetContext #[`mlir_env, `mlir_operation] (extra := #[thms])
  let procs :=
    #[←
        if h : 0 < facts.size then
          argsSimprocs facts[0]
        else
          Simp.getSimprocs,
      ← ({} : Simp.Simprocs).add ``readThroughWrites (post := false),
      ← memSimprocs (← MemCtx.build), ← ({} : Simp.Simprocs).add ``readThroughStore (post := true),
      ← ({} : Simp.Simprocs).add ``gepValue (post := true)]
  let elaborated ← elabSimpArgs simpArgs ctx procs (eraseLocal := false) (kind := .simp)
  return (←
        simp e elaborated.ctx (simprocs := elaborated.simprocs) (discharge? := decideDischarge)).1

/-- The state equations `S = …` in context -/
def stateFacts : MetaM (Array FVarId) := do
  (← localEqs).filterMapM fun e => do
      let state := e.lhs.isFVar && (← inferType e.lhs).isConstOf ``GlobalState
      return if state then some e.decl.fvarId else none

/-- The equations `x = _` of the locals in `e`: the state `S = …` and the step values `v = …`
it reads, but not those of values named with `with` (`tagNamed`) or of stack slots, which stay
folded. -/
private def valueStateFacts (e : Expr) : MetaM (Array FVarId) := do
  let xs := (collectFVars {} e).fvarSet
  (← localEqs).filterMapM fun q => do
      let .fvar x := q.lhs | return none
      if !xs.contains x || isNamedEq (← instantiateMVars q.decl.type) then
        return none
      return some q.decl.fvarId

/-- The local facts `E.read r = v` (a pattern lemma's inputs): read resolution goes through them as
through `hE`. -/
def readFacts : MetaM (Array FVarId) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then
        return acc
      let reads ←
        (← conjuncts d.toExpr (← instantiateMVars d.type)).anyM fun (_, ty) =>
            return ty.eq?.any (·.2.1.isAppOf ``Env.read)
      return if reads then acc.push d.fvarId else acc

/-- `e` with each proof in it that mentions locals but proves a closed fact by `decide` (`x[0]`'s
`0 < 8`, proved through the args fact), or a lane bound `↑i < n` of an `ofFn`'s `i : Fin n` by
`i.isLt`, so sealing can clear those locals. Equal by proof irrelevance. -/
def closeProofs (e : Expr) : MetaM Expr := do
  let outer ← getLCtx
  Meta.transform e (pre := fun t => do
      unless t.hasFVar do
        return .done t
      unless ← isProof t do
        return .continue
      -- beta-reduced: an `Eq.ndrec` motive's redex may mention locals the fact doesn't
      let ty ← Core.betaReduce (← instantiateMVars (← inferType t))
      if ty.hasMVar || ty.hasAnyFVar outer.contains then
        return .continue
      if ty.hasFVar then
        -- only binders of `e` itself: a lane index's bound
        let some (_, _, lhs, _) := ty.app4? ``LT.lt | return .continue
        let some i := lhs.app2? ``Fin.val |>.map (·.2) | return .continue
        let pf ← mkAppM ``Fin.isLt #[i]
        unless ← isDefEq (← inferType pf) ty do
          return .continue
        return .done pf
      let some pf ← decideProof? ty | return .continue
      return .done pf)

/-- `e` with each literal vector that is a `mlir_const` constant's value as that constant: equal by
unfolding it, so no proof. Both sides are literals, so comparing them is cheap. -/
def foldConsts (e : Expr) : MetaM Expr := do
  let consts ← labelled `mlir_const
  if consts.isEmpty then
    return e
  let mut cands : Array (Expr × Expr) := #[]
  for n in consts do
    let some v ←
      (do
            let c ← mkConstWithFreshMVarLevels n
            return (← unfoldDefinition? c)) <|>
          pure none | continue
    cands := cands.push (mkConst n, v)
  Meta.transform e (post := fun t => do
      unless t.isAppOf ``Vector.mk || t.isAppOf ``Vector.set || t.isAppOf ``Vector.replicate do
        return .continue
      if t.hasFVar || t.hasMVar then
        return .continue
      for (c, v) in cands do
        -- default transparency: numerals differ in spelling (`43#64`, `(43 : BitVec 64)`)
        if v.getAppFn == t.getAppFn && (← withNewMCtxDepth (withDefault (isDefEq t v))) then
          return .done c
      return .continue)

/-- Resolve the reads in `e`: arguments first, against `argsFact : E.args = _`,
then values, unfolding the write chain with `chainFact : E = _`.
Unfolding first would send the argument reads past `E` down to the root env. -/
def simpValue (only : Bool) (simpArgs : Syntax) (e : Expr) (env : Expr) (expand : Bool) :
    TacticM Simp.Result := do
  let argsFact := (← findEqWithLhs? (← mkAppM ``Env.args #[env]) m!"`{env}.args = _`").toArray
  let chainFact := (← findEqWithLhs? env m!"`{env} = _`").toArray
  let reads ← readFacts
  let args ← simpPass only simpArgs e argsFact
  let vals ← simpPass true simpArgs args.expr (chainFact ++ reads)
  let r ← args.mkEqTrans vals
  let facts ←
    if expand then
      valueStateFacts r.expr
    else
      stateFacts
  -- also without facts: the reads were resolved by `simp only`, the simp set not yet run
  let r ←
    if facts.isEmpty && only then
      pure r
    else
      r.mkEqTrans (← simpPass only simpArgs r.expr (argsFact ++ facts ++ reads))
  -- last: `#v[.value x, …]` to `Ty.wrap #v[x, …]`, once every lane is final
  let ctx ← Simp.mkContext
  let (p, _) ← simp r.expr ctx (simprocs := #[← ({} : Simp.Simprocs).add ``pullWrap (post := true)])
  let r ← r.mkEqTrans p
  return { r with expr := ← foldConsts (← closeProofs r.expr) }

end ResolveReads

end

end LeanMLIR.RIR.Tactic

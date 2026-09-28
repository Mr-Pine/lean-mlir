module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.Tactic.Parse
public import SSA.Projects.RIR.Run.Tactic.Util
public import SSA.Projects.RIR.Run.Tactic.Memory
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealState

structure SealedState where
  S' : FVarId
  hS' : FVarId
  hS : FVarId

/-- The new state with its projections reduced -/
def dsimpState (e : Expr) : MetaM Expr := do
  return (← dsimp e (← Simp.mkContext)).1

/-- `transportDischarge`'s search, with the context's facts by (instantiated) type. -/
partial def transportWith (facts : Std.HashMap Expr Expr) (lemmas : Array Name) (fuel : Nat)
    (p : Expr) : MetaM (Option Expr) := do
  if let some h := facts[p]? then
    return some h
  if fuel = 0 then
    return none
  for n in lemmas do
    let saved ← saveState
    let m ← mkFreshExprMVar p
    let pf? ←
      (do
            let gs ← withReducible (m.mvarId!.apply (← mkConstWithFreshMVarLevels n))
            for g in gs do
              if ← g.isAssigned then
                continue
              let some pf ←
                transportWith facts lemmas (fuel - 1)
                    (← instantiateMVars (← g.getType)) | return none
              g.assign pf
            return some (← instantiateMVars m)) <|>
          pure none
    if pf?.isSome then
      return pf?
    restoreState saved
  -- a fact equal only up to reducible unfolding
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← withReducible (isDefEq d.type p)) then
      return some d.toExpr
  return none

/-- Prove `p` from the context and the `mlir_transport` lemmas, at reducible transparency:
`LimbsFit` of a store chain is its base's fact. -/
def transportDischarge (fuel : Nat) (p : Expr) : MetaM (Option Expr) := do
  let mut facts : Std.HashMap Expr Expr := {}
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      facts := facts.insert (← instantiateMVars d.type) d.toExpr
  transportWith facts (← labelled `mlir_transport) fuel (← instantiateMVars p)

/-- The new state simplified by `mlir_state` and `readThroughStore`; side conditions are
discharged from the context, at reducible transparency. -/
def simpState (e : Expr) : MetaM Simp.Result := do
  let some ext ← getSimpExtension? `mlir_state | throwError "no `mlir_state` simp set"
  let ctx ←
    Simp.mkContext (simpTheorems := #[← ext.getTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let procs := #[← Simp.getSimprocs, ← ({} : Simp.Simprocs).add ``readThroughStore (post := true)]
  -- the context's facts, once for all side conditions
  let mut facts : Std.HashMap Expr Expr := {}
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      facts := facts.insert (← instantiateMVars d.type) d.toExpr
  let lemmas ← labelled `mlir_transport
  -- reducible: a side condition's `assumption` must not unfold memory chains
  let disch : Simp.Discharge := fun p => do
    -- a fact, as is or `mlir_state`-normalized (a store chain's `LimbsFit` is its base's); the
    -- transport search last
    let p ← instantiateMVars p
    if let some pf := facts[p]? then
      return some pf
    let (r, _) ← simp p ctx (simprocs := procs)
    if let some pf := facts[r.expr]? then
      return some (← mkEqMPR (← r.getProof) pf)
    if let some pf← withReducible (Simp.dischargeDefault? p) then
      return some pf
    transportWith facts lemmas 64 p
  return (← simp e ctx (simprocs := procs) (discharge? := disch)).1

/-- Close the goal by `transportDischarge`: a fact of the context, through `mlir_transport`
lemmas. -/
elab "transport_fact" : tactic =>
  withMainContext do
    let mut g ← getMainGoal
    -- a state `S` with `hS : S = e` in the goal: the facts are about `e`
    for x in (collectFVars {} (← instantiateMVars (← g.getType))).fvarIds do
      unless (← g.withContext (inferType (.fvar x))).isConstOf ``GlobalState do
        continue
      if let some h← g.withContext (findEqWithLhs? (.fvar x) m!"") then
        g := (← substCore g h (symm := false)).2
    g.withContext do
        let some pf ←
          transportDischarge 64
              (← instantiateMVars (← g.getType)) | throwError "`transport_fact`: no transport"
        g.assign pf
    replaceMainGoal []

def sealState (S : Expr) : TacticM SealedState :=
  withMainContext do
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    let S' := runBodyFrom.state
    let hS ← findEqWithLhs S m!"of the form `{S} = _`"
    let some (_, _, S₀chain) :=
      (← instantiateMVars (← hS.getType)).eq? | throwError "expected an equation"
    -- new state as function of the old one
    let abstract := Expr.lam `s (← inferType S) (← kabstract S' S) .default
    let new ← dsimpState (abstract.beta #[S₀chain])
    let r ← simpState new
    let hNew := mkExpectedPropHint (← mkCongrArg abstract (.fvar hS)) (← mkEq S' new)
    let (fvs, g) ←
      generalizeOpaque g (hyps := #[]) S' `S'
          #[⟨`hS', (mkEq · r.expr), ← mkEqTrans hNew (← r.getProof)⟩]
    replaceMainGoal [g]
    return ⟨fvs[0]!, fvs[1]!, hS⟩

/-- Name the goal's state `S`, with `hS : S = s`, unless it has an equation already: a loop's
proof starts from a bare state `s`, a loop's continuation from a term over an earlier state. That
state's facts are carried over to `S`, and `s` is simplified as a step's new state is. -/
def ensureStateEq : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    -- inside a block, or at a block's start (a loop's continuation)
    let s ←
      try
        pure (← getRunBodyFrom goal).state
      catch _ =>
        pure (← getFuncRunFromGoal goal).state
    if (← findEqWithLhs? s m!"`{s} = _`").isSome then
      return
    -- a state built on an earlier one `b` (`b.mem`, `b.alloc`): `b`'s facts, carried to it
    let mut g := g
    let mut carried := #[]
    let mut olds := #[]
    let mut seen : Std.HashSet Expr := {}
    let bases := (← IO.mkRef #[])
    s.forEachWhere
        (fun e => e.isAppOfArity ``GlobalState.mem 1 || e.isAppOfArity ``GlobalState.alloc 1)
        fun e => bases.modify (·.push e.appArg!)
    for b in (← bases.get).toList.eraseDups do
      if b == s then
        continue
      for d in ← getLCtx do
        if d.isImplementationDetail || !(← isProp d.type) then
          continue
        let ty ← instantiateMVars d.type
        -- facts of the state itself (`b.WF`, `b.mem.LimbsFit p`), not equations
        if ty.isEq || !(ty.getAppArgs.any fun a => a == b || a.getAppArgs.contains b) then
          continue
        let ty' := ty.replace fun t => if t == b then some s else none
        -- once per fact: `h6` and `h6S` may state the same about `s`
        if seen.contains ty' then
          continue
        seen := seen.insert ty'
        let some pf ← transportDischarge 64 ty' | continue
        let (h, g') ← (← g.assert d.userName ty' pf).intro1P
        g := g'
        carried := carried.push h
        olds := olds.push d.fvarId
    -- simplified like a step's new state: reads through the stores resolve
    let r ←
      g.withContext do
          simpState s
    let (_, g') ←
      g.withContext do
          generalizeOpaque g (hyps := carried) s `S #[⟨`hS, (mkEq · r.expr), ← r.getProof⟩]
    -- the originals are about a state that is gone
    replaceMainGoal [← g'.tryClearMany olds]

end SealState

end

end LeanMLIR.RIR.Tactic

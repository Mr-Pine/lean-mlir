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

/-- Prove `p` from the context and the `mlir_transport` lemmas, at reducible transparency:
`LimbsFit` of a store chain is its base's fact. -/
def transportDischarge (fuel : Nat) (p : Expr) : MetaM (Option Expr) := do
  transportWith (← contextFactMap) (← labelled `mlir_transport) fuel (← instantiateMVars p)

/-- The new state simplified by `mlir_state` and the memory simprocs (reads through stores, by read
facts, through `hS`); side conditions are discharged from the context, at reducible transparency. -/
def simpState (e : Expr) : MetaM Simp.Result := do
  let some ext ← getSimpExtension? `mlir_state | throwError "no `mlir_state` simp set"
  let ctx ←
    Simp.mkContext (simpTheorems := #[← ext.getTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let dischProcs :=
    #[← Simp.getSimprocs, ← ({} : Simp.Simprocs).add ``readThroughStore (post := true)]
  let procs := dischProcs.push (← memSimprocs)
  -- the context's facts, once for all side conditions
  let facts ← contextFactMap
  let lemmas ← labelled `mlir_transport
  -- reducible: a side condition's `assumption` must not unfold memory chains
  let disch : Simp.Discharge := fun p => do
    -- a fact, as is or `mlir_state`-normalized (a store chain's `LimbsFit` is its base's); the
    -- transport search last
    let p ← instantiateMVars p
    if let some pf := facts[p]? then
      return some pf
    -- side conditions (`LimbsFit`, `Fits`) read no memory
    let (r, _) ← simp p ctx (simprocs := dischProcs)
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

/-- The memory facts of the step's new state `new` (over the old state `S`), each `(h, motive)` with
`h : motive new`: every write an `mlir_read` lemma reads back, and every read fact of `S` the
writes miss (one they overwrite is dropped). Asserted in `g`; the old read facts returned, for
clearing once the state is sealed. Read through the writes while `S`'s facts hold. -/
def memFactsOf (g : MVarId) (S new : Expr) :
    MetaM (Array (FVarId × Expr) × Array FVarId × MVarId) :=
  g.withContext do
    let newMem ← normWidths (← dsimpState (← mkAppM ``GlobalState.mem #[new]))
    let oldMem ← mkAppM ``GlobalState.mem #[S]
    let c ← MemCtx.build
    -- the fact `read e = v` at `new`: `motive new` with `motive s := read (e at s.mem) = v`
    let motiveOf (e v : Expr) : MetaM Expr := memMotive e newMem (mkEq · v)
    let mut g := g
    let mut hyps := #[]
    -- an `alloca`'s fresh slot fits its bytes: `Fits (S.alloca n).mem S.allocaPtr (8 * n)`
    if new.isAppOfArity ``GlobalState.alloca 2 then
      let n := new.getArg! 1
      let ptr ← mkAppM ``GlobalState.allocaPtr #[S]
      let w ← normWidths (← mkAppM ``HMul.hMul #[mkNatLit 8, n])
      let motive ←
        withLocalDeclD `s (mkConst ``GlobalState) fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Fits #[← mkAppM ``GlobalState.mem #[x], ptr, w])
      let pf ← mkAppOptM ``Fits.allocaPtr #[w, n, S, ← mkAppM ``Nat.le_refl #[w]]
      let (h, g') ← (← g.assert `hfits (motive.beta #[new]) pf).intro1P
      g := g'
      hyps := hyps.push (h, motive)
    let mut seen : Array Expr := #[]
    -- the writes read back: an `mlir_read` lemma's read of each write, at the new memory
    for w in ← writesOf newMem do
      for l in c.lemmas do
        unless w.isAppOf l.write do
          continue
        let read? ←
          observing? do
              let (_, _, concl) ←
                forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels l.name))
              let some (_, lhs, _) := concl.eq? | failure
              let some wpat := lhs.getAppArgs.find? (·.isApp) | failure
              unless ← withReducible (isDefEq wpat w) do
                failure
              instantiateMVars (lhs.replace fun t => if t == wpat then some newMem else none)
        let some e := read? | continue
        if seen.contains e || e.hasMVar then
          continue
        seen := seen.push e
        let (v, pf) ← readThrough c e
        -- unresolved: a write no lemma reads back or past
        if v == e || (v.find? (· == newMem)).isSome then
          continue
        -- the value's own reads of `S` by `S`'s facts
        let r ← simpState v
        let (v, pf) := (r.expr, ← mkEqTrans pf (← r.getProof))
        let motive ← motiveOf e v
        -- named after the pointer read, so facts at distinct pointers stay accessible
        -- (`q.add k` after `q` and `k`)
        let ptr? ←
          e.getAppArgs.findM? fun a => do
              return (← inferType a).isConstOf ``Pointer
        let name ←
          match ptr? with
          | some (.fvar x) =>
            pure ((`hread).appendAfter s!"_{← x.getUserName}")
          | some a =>
            do
              let some (.fvar x, off) := a.app2? ``Pointer.add | pure `hread
              let k ←
                (do
                      return (← getBitVecValue? off).map (·.2.toNat)) <|>
                    pure none
              pure ((`hread).appendAfter s!"_{← x.getUserName}_{k.getD 0}")
          | none =>
            pure `hread
        let (h, g') ← (← g.assert name (motive.beta #[new]) pf).intro1P
        g := g'
        hyps := hyps.push (h, motive)
    -- the read facts of `S` carried through the writes; the old ones kept for sealing the state
    let mut olds := #[]
    for d in ← getLCtx do
      let some (l, y) := memReadFact? c.heads S (← instantiateMVars d.type) | continue
      let e := l.replace fun t => if t == oldMem then some newMem else none
      let (r, pf) ← readThrough c e
      -- past the writes, or through one inside it (`spliceBits (S.mem.readAt p v) off x`): the
      -- old read by its value
      let at_ ←
        withLocalDeclD `z (← inferType l) fun z => do
            mkLambdaFVars #[z] (r.replace fun t => if t == l then some z else none)
      let y' ← Tactic.normWidths (at_.beta #[y])
      if
          (r.find? (· == l)).isSome && (y'.find? (· == S)).isNone &&
            (y'.find? (· == newMem)).isNone then
        let motive ← motiveOf e y'
        let pf ← mkEqTrans pf (← mkCongrArg at_ d.toExpr)
        let (h, g') ← (← g.assert d.userName (motive.beta #[new]) pf).intro1P
        g := g'
        hyps := hyps.push (h, motive)
      olds := olds.push d.fvarId
    return (hyps, olds, g)

def sealState (S : Expr) (hyps : Array (FVarId × Expr) := #[]) : TacticM SealedState :=
  withMainContext do
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    let S' := runBodyFrom.state
    let hS ← findEqWithLhs S m!"of the form `{S} = _`"
    -- the new state over the old one, `S`, whose facts the simplification's side conditions use
    -- widths as literals, as the facts have them: transport lemmas unify at reducible transparency
    let new ← Tactic.normWidths (← dsimpState S')
    let r ← simpState new
    let hNew := mkExpectedPropHint (← mkEqRefl S') (← mkEq S' new)
    let (fvs, g) ←
      generalizeOpaque g (hyps := #[]) S' `S'
          #[⟨`hS', (mkEq · r.expr), ← mkEqTrans hNew (← r.getProof)⟩]
    -- `hyps`, `h : motive (S'`'s term)`, about `S'`: `S'`'s term `= S'` by `hS'`
    let mut g := g
    if !hyps.isEmpty then
      let hRaw ←
        g.withContext do
            mkEqTrans (← mkEqTrans hNew (← r.getProof)) (← mkEqSymm (.fvar fvs[1]!))
      for (h, motive) in hyps do
        g ←
          g.withContext do
              -- `Eq.ndrec` built directly: `mkEqNDRec` infers the types of the state's big terms
              let pf :=
                mkAppN (mkConst ``Eq.ndrec [.zero, .succ .zero])
                  #[mkConst ``GlobalState, S', motive, .fvar h, .fvar fvs[0]!, hRaw]
              let (_, g') ← (← g.assert (← h.getUserName) (motive.beta #[.fvar fvs[0]!]) pf).intro1P
              g'.clear h
    replaceMainGoal [g]
    return ⟨fvs[0]!, fvs[1]!, hS⟩

/-- Name the goal's state `S`, with `hS : S = s`, unless it has an equation already: a loop's
proof starts from a bare state `s`, a loop's continuation from a term over an earlier state. The
facts of `s` (or of the earlier state) are carried over to `S`, and `s` is simplified as a step's
new state is. -/
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
    -- a bare state's own facts (`Fits s.mem p w`, `s.mem.readAt p w = x`), generalized with it:
    -- about `S`, so each seal transports them
    if s.isFVar then
      let heads ← readHeads
      for h in ← g.withContext (hypsMentioning s) do
        let ty ← instantiateMVars (← g.withContext h.getType)
        -- facts and memory reads, not other equations nor continuations
        if
            (← g.withContext (isProp ty)) && (!ty.isEq || (memReadFact? heads s ty).isSome) &&
              !ty.isForall then
          carried := carried.push h
    -- simplified like a step's new state: reads through the stores resolve
    let r ←
      g.withContext do
          simpState s
    let (fvs, g') ←
      g.withContext do
          generalizeOpaque g (hyps := carried) s `S #[⟨`hS, (mkEq · r.expr), ← r.getProof⟩]
    g ← g'.tryClearMany olds
    -- a bare state's memory where its facts say it fits: `S.mem.readAt q w = s.mem.readAt q w`,
    -- carried past the writes that miss it, so reads below them resolve to `s`'s
    if s.isFVar then
      g ←
        g.withContext do
            let S := mkFVar fvs[0]!
            let mut g₁ := g
            let mut seen : Array (Expr × Expr) := #[]
            let facts ← splitConjunctedFacts
            let heads ← readHeads
            let known ←
              facts.filterMapM fun (_, ty) => do
                  let some (l, _) := memReadFact? heads S ty | return none
                  return some (← normWidths l)
            for (_, ty) in facts do
              let_expr Fits m q w := ty | continue
              unless m.isAppOfArity ``GlobalState.mem 1 && m.appArg! == S && q.isFVar do
                continue
              let w ← normWidths w
              if seen.contains (q, w) then
                continue
              seen := seen.push (q, w)
              let motive ←
                withLocalDeclD `x (mkConst ``GlobalState) fun x => do
                    mkLambdaFVars #[x]
                        (← mkAppM ``MemoryState.readAt #[← mkAppM ``GlobalState.mem #[x], q, w])
              -- not where a read fact already gives the value
              if known.contains (motive.beta #[S]) then
                continue
              let pf ← mkCongrArg motive (mkFVar fvs[1]!)
              let name := (`hread).appendAfter s!"_{← q.fvarId!.getUserName}"
              let ty ← mkEq (motive.beta #[S]) (motive.beta #[s])
              let (_, g') ← (← g₁.assert name ty pf).intro1P
              g₁ := g'
            return g₁
    replaceMainGoal [g]

end SealState

end

end LeanMLIR.RIR.Tactic

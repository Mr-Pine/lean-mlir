module

public import MLIR.Semantics.Func
public import MLIR.Run.Tactic.Parse
public import MLIR.Run.Tactic.Util
public import MLIR.Run.Tactic.Memory
public meta import Lean.Elab.Tactic

namespace MLIR.Tactic

open Lean Elab Tactic Meta

public meta section

section SealState

structure SealedState where
  S' : FVarId
  hS' : FVarId
  hS : FVarId

/-- The new state simplified by `mlir_state` and the memory simprocs (reads through stores, by read
facts, through `hS`); side conditions are discharged from the context (`c?`, else gathered), at
reducible transparency. -/
def simpState (e : Expr) (c? : Option MemCtx := none) : MetaM Simp.Result := do
  let ctx ← simpSetContext #[`mlir_state]
  let c ← c?.getDM MemCtx.build
  let dischProcs := #[← Simp.getSimprocs]
  let procs := dischProcs.push (← memSimprocs c)
  -- reducible: a side condition's `assumption` must not unfold memory chains
  let disch : Simp.Discharge := fun p => do
    -- from the facts, as is or `mlir_state`-normalized (a store chain's `LimbsFit` is its base's);
    -- the transport search last
    let p ← instantiateMVars p
    if let some pf := c.factMap[p]? then
      return some pf
    -- side conditions (`LimbsFit`, `Fits`) read no memory
    let (r, _) ← simp p ctx (simprocs := dischProcs)
    if let some pf := c.factMap[r.expr]? then
      return some (← mkEqMPR (← r.getProof) pf)
    if let some pf← withReducible (Simp.dischargeDefault? p) then
      return some pf
    factDischarge c.toFactCtx 64 p
  return (← simp e ctx (simprocs := procs) (discharge? := disch)).1

/-- Substitute each state local of `e` that has an equation `x = _` by it. -/
def substStates (g : MVarId) (e : Expr) : MetaM MVarId := do
  let mut g := g
  for x in (collectFVars {} e).fvarIds do
    g ←
      g.withContext do
          unless (← getLCtx).contains x && (← x.getType).isConstOf ``GlobalState do
            return g
          let some h ← findEqWithLhs? (.fvar x) | return g
          return (← substCore g h (symm := false)).2
  return g

/-- `h : l = r` with `r`'s projections reduced (`dsimpState`). -/
def dsimpStateEq (g : MVarId) (h : FVarId) : MetaM MVarId :=
  g.withContext do
    let some (_, l, r) := (← instantiateMVars (← h.getType)).eq? | return g
    g.replaceLocalDeclDefEq h (← mkEq l (← dsimpState r))

/-- Close `g` by `factDischarge`: its searches, then the transport search, about a state `S` with
`hS : S = s` from the facts about `s`. -/
def memFact (g : MVarId) : MetaM Bool :=
  g.withContext do
    -- a local, before gathering the facts
    if let some h← withReducible (findLocalDeclWithType? (← g.getType)) then
      g.assign (mkFVar h)
      return true
    if let some pf← factDischarge (← FactCtx.build) 0 (← g.getType) then
      g.assign pf
      return true
    let saved ← saveState
    let g' ← substStates g (← instantiateMVars (← g.getType))
    let ok ←
      g'.withContext do
          let some pf ← factDischarge (← FactCtx.build) 64 (← g'.getType) | return false
          g'.assign pf
          return true
    unless ok do
      saved.restore
    return ok

/-- Close a side condition from the facts (`memFact`): `Fits`, disjointness, `≠`, a closed fact by
`decide`, or a fact carried by `mlir_transport` lemmas. -/
elab "mem_fact" : tactic =>
  withMainContext do
    let g ← getMainGoal
    unless ← memFact g do
      throwError "`mem_fact`: not from the facts{indentExpr (← g.getType)}"
    replaceMainGoal []

/-- The memory facts of the step's new state `new` (over the old state `S`), each `(h, motive)` with
`h : motive new`: a new block's size (`mlir_fresh`), every write an `mlir_read` lemma reads back,
and every read fact of `S` the writes miss (the others dropped, traced by `trace.rir`). Asserted in
`g`; the old read facts returned, for clearing once the state is sealed. Read through the writes
while `S`'s facts hold. -/
def memFactsOf (g : MVarId) (S new : Expr) :
    MetaM (Array (FVarId × Expr) × Array FVarId × MVarId) :=
  g.withContext do
    let newMem ← normWidths (← dsimpState (← mkAppM ``GlobalState.mem #[new]))
    let oldMem ← mkAppM ``GlobalState.mem #[S]
    let c ← MemCtx.build
    -- `(name, fact about newMem, proof)`, asserted last
    let mut facts : Array (Name × Expr × Expr) := #[]
    -- a new block's size: each `mlir_fresh` lemma's `Fits` at the new memory
    for n in ← labelled `mlir_fresh do
      let some fact ←
        observing? do
            let lem ← mkConstWithFreshMVarLevels n
            let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
            let_expr Fits m _ _ := concl | failure
            unless ← withReducible (isDefEq m newMem) do
              failure
            for mv in ms do
              let mv := mv.mvarId!
              if !(← mv.isAssigned) && (← isProp (← mv.getType)) then
                let some pf ← factDischarge c.toFactCtx 4 (← mv.getType) | failure
                mv.assign pf
            unless ← ms.allM (·.mvarId!.isAssigned) do
              failure
            return (← normWidths (← instantiateMVars concl),
                ← instantiateMVars (mkAppN lem ms)) | continue
      facts := facts.push (`hfits, fact)
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
        -- past the write to a read of `S` with a fact: that fact is carried below, not read back
        if c.reads.contains (← normWidths v) then
          continue
        -- the value's own reads of `S` by `S`'s facts
        let r ← simpState v c
        let (v, pf) := (r.expr, ← mkEqTrans pf (← r.getProof))
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
        facts := facts.push (name, ← mkEq e v, pf)
    -- the read facts of `S` carried through the writes; the old ones kept for sealing the state
    let mut olds := #[]
    for d in ← getLCtx do
      let some (l, y) := memReadFact? c.heads S (← instantiateMVars d.type) | continue
      let e := l.replace fun t => if t == oldMem then some newMem else none
      let (r, pf) ← readThrough c e
      -- past the writes, or through one inside it (`spliceBits (S.mem.readAt p v) off x`): the
      -- old read by its value
      let at_ ← motiveOver r l (← inferType l)
      let y' ← Tactic.normWidths (at_.beta #[y])
      if
          (r.find? (· == l)).isSome && (y'.find? (· == S)).isNone &&
            (y'.find? (· == newMem)).isNone then
        let pf ← mkEqTrans pf (← mkCongrArg at_ d.toExpr)
        facts := facts.push (d.userName, ← mkEq e y', pf)
      else
        -- overwritten, or past a write not known to miss it (possibly aliasing)
        let stuck := (← writesOf newMem).any fun w => (r.find? (· == w)).isSome
        let why := if stuck then "a write not known to miss it" else "overwritten"
        trace[rir] m!"read fact {d.userName} dropped ({why}):{indentExpr r}"
      olds := olds.push d.fvarId
    -- each fact as `h : motive new`, `motive s` the fact with `s.mem` for the new memory
    let mut g := g
    let mut hyps := #[]
    for (name, ty, pf) in facts do
      let motive ← memMotive ty newMem
      let (h, g') ← (← g.assert name (motive.beta #[new]) pf).intro1P
      g := g'
      hyps := hyps.push (h, motive)
    return (hyps, olds, g)

def sealState (S : Expr) (hyps : Array (FVarId × Expr) := #[]) : TacticM SealedState :=
  withMainContext do
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    let S' := runBodyFrom.state
    let hS ← findEqWithLhs S
    -- the new state over the old one, `S`, whose facts the simplification's side conditions use
    -- widths as literals, as the facts have them: transport lemmas unify at reducible transparency
    let new ← Tactic.normWidths (← dsimpState S')
    let r ← simpState new
    let hNew := mkExpectedPropHint (← mkEqRefl S') (← mkEq S' new)
    let (fvs, g) ←
      generalizeOpaque g S' `S' #[⟨`hS', (mkEq · r.expr), ← mkEqTrans hNew (← r.getProof)⟩]
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

/-- `target`, the fact `h : ty` restated about a later state, by `mlir_transport` lemmas and the
local implications `locals` from `h` (also `dsimp`ed as states are), their premises from the facts
`c` (also by `premiseSearch?`): two lemmas deep, else (`deep`) deeper. -/
def carryFact (c : FactCtx) (locals : Array Expr) (h ty target : Expr) (deep := true) :
    MetaM (Option Expr) := do
  let facts := (c.factMap.insert ty h).insert (← dsimpState ty) h
  let side := premiseSearch? c
  if let some pf← transportWith facts c.transport 2 target locals side then
    return some pf
  if !deep then
    return none
  transportWith facts c.transport 64 target locals side

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
    if (← findEqWithLhs? s).isSome then
      return
    -- a state built on an earlier one `b` (`b.mem`, `b.alloc`): `b`'s facts, carried to it
    let mut g := g
    let mut carried := #[]
    let mut olds := #[]
    let mut seen : Std.HashSet Expr := {}
    let fc ← FactCtx.build
    let locals ← localImplications
    let bases := (← IO.mkRef #[])
    s.forEachWhere
        (fun e => e.isAppOfArity ``GlobalState.mem 1 || e.isAppOfArity ``GlobalState.alloc 1)
        fun e => bases.modify (·.push e.appArg!)
    let bases := (← bases.get).toList.eraseDups
    for b in bases do
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
        let some pf ← carryFact fc locals d.toExpr ty ty' | continue
        let (h, g') ← (← g.assert d.userName ty' pf).intro1P
        g := g'
        carried := carried.push h
        olds := olds.push d.fvarId
    -- the earlier state, a local (a loop's start): its reads carried past the writes over it, and
    -- the writes read back, as a step's
    let base? := bases.find? fun b => b.isFVar && b != s
    if let some b := base? then
      let (hyps, oldReads, g') ← memFactsOf g b s
      g := g'
      carried := carried ++ hyps.map (·.1)
      olds := olds ++ oldReads
    let heads ←
      if s.isFVar then
        readHeads
      else
        pure #[]
    -- a bare state's own facts (`Fits s.mem p w`, `s.mem.readAt p w = x`), generalized with it:
    -- about `S`, so each seal transports them
    if s.isFVar then
      for h in ← g.withContext (hypsMentioning s) do
        let ty ← instantiateMVars (← g.withContext h.getType)
        -- facts and memory reads, not other equations nor continuations
        if
            (← g.withContext (isProp ty)) && (!ty.isEq || (memReadFact? heads s ty).isSome) &&
              !ty.isForall &&
              !(← g.withContext (isContinuation ty)) then
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
              let read ← mkAppM ``MemoryState.readAt #[m, q, w]
              -- not where a read fact already gives the value
              if known.contains read then
                continue
              let motive ← memMotive read m
              let pf ← mkCongrArg motive (mkFVar fvs[1]!)
              let name := (`hread).appendAfter s!"_{← q.fvarId!.getUserName}"
              let ty ← mkEq read (motive.beta #[s])
              let (_, g') ← (← g₁.assert name ty pf).intro1P
              g₁ := g'
            return g₁
    replaceMainGoal [g]

end SealState

end

end MLIR.Tactic

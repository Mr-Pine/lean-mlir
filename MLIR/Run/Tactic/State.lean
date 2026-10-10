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

/-- `h : S = s` with `s`'s writes merged with the writes below them by the `mlir_state` lemmas
(`(m.storeAt p u).storeAt (p.add k) y = …`): the new state's simplification sees no write below,
the old state being a local. Side conditions from the facts. -/
def mergeStateEq (g : MVarId) (h : FVarId) : MetaM MVarId :=
  g.withContext do
    let some (_, S, s) := (← instantiateMVars (← h.getType)).eq? | return g
    let c ← FactCtx.build
    let disch : Simp.Discharge := fun p => do
      factDischarge c 0 (← instantiateMVars p)
    let (r, _) ← simp s (← simpSetContext #[`mlir_state]) (discharge? := disch)
    if r.expr == s then
      return g
    -- typed as the result: an `rfl` lemma's step has no proof
    let ty ← mkEq S r.expr
    return (← g.replace h (← mkEqTrans (mkFVar h) (← r.getProof)) (type? := ty)).mvarId

/-- Close `g` by `factDischarge`: its searches, then the transport search, about a state `S` with
`hS : S = s` from the facts about `s`. -/
def memFact (g : MVarId) : MetaM Bool :=
  g.withContext do
    -- a local, before gathering the facts
    if let some h← withReducible (findLocalDeclWithType? (← g.getType)) then
      g.assign (mkFVar h)
      return true
    -- the searches, then two lemmas deep from the facts as they are (an object fact's projections),
    -- before the deep search through the states' equations
    let c ← FactCtx.build
    if let some pf← factDischarge c 0 (← g.getType) then
      g.assign pf
      return true
    if let some pf← factDischarge c 2 (← g.getType) then
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

/-- `base` after the local pointer `p`: `base_x` for `x`, `base_x_k` for `x.add k#64`; else
`base`. -/
def namedAfterPtr (base : Name) (p : Expr) : MetaM Name := do
  match p with
  | .fvar x =>
    return base.appendAfter s!"_{← x.getUserName}"
  | _ =>
    let some (.fvar x, off) := p.app2? ``Pointer.add | return base
    let k ←
      (do
            return (← getBitVecValue? off).map (·.2.toNat)) <|>
          pure none
    return base.appendAfter s!"_{← x.getUserName}_{k.getD 0}"

/-- A fact matching `ty`, a premise with open values, by unification: a memory predicate from one
of its kind or a stronger one (`weakenMemPred`). -/
def factMatching? (facts : Array (Expr × Expr)) (ty : Expr) : MetaM (Option Expr) := do
  for (pf, fty) in facts do
    let pf? ←
      observing? do
          match memPred? ty, memPred? fty with
          | some (j, _), some (k, m, p, w) =>
            unless j ≤ k do
              failure
            unless ← withReducible (isDefEq ty (← mkAppM memPreds[j]! #[m, p, w])) do
              failure
            weakenMemPred pf k j
          | _, _ =>
            unless ← withReducible (isDefEq ty fty) do
              failure
            pure pf
    if let some pf := pf? then
      return some pf
  return none

/-- The memories below `m` down to a local state's, outermost first, for fresh facts: `m`'s writes,
the memory they start from (a new block's), an abbreviation's own writes after it (`storeOut m …`
unfolded at reducible transparency). -/
partial def freshLayers (m : Expr) : MetaM (Array Expr) := do
  -- a local state's memory: the old one
  if m.isAppOfArity ``GlobalState.mem 1 && m.appArg!.isFVar then
    return #[]
  if let some c := m.getAppFn.constName? then
    if (← isReducible c) && !(← isProjectionFn c) then
      if let some m' ← withReducible (unfoldDefinition? m) then
        let m' := m'.headBeta
        if m' != m then
          return #[m] ++ (← freshLayers m')
  for a in m.getAppArgs do
    if (← inferType a).isConstOf ``MemoryState then
      return #[m] ++ (← freshLayers a)
  return #[m]

/-- The pointer a fact `P m p …` is about: its first `Pointer` argument. -/
def factPtr? (ty : Expr) : MetaM (Option Expr) :=
  ty.getAppArgs.findM? fun a => return (← inferType a).isConstOf ``Pointer

/-- The name of a fresh fact `concl` about the pointer `p`: a memory predicate's (`hfits_x`); an
object's, the fact about the old memory `oldMem` of the lemma's premise `prem` about the same
object, which it supersedes (`hx_limbs`, `LimbsRoom` to `LimbsFit`), else `hlimbsFit_x`. -/
def freshName (c : MemCtx) (concl : Expr) (oldMem : Expr) (prems : Array Expr) :
    MetaM (Name × Option FVarId) := do
  if let some (k, _, p, _) := memPred? concl then
    return (← namedAfterPtr #[`hbounds, `hroom, `hfits][k]! p, none)
  let some p ← factPtr? concl | return (`hfresh, none)
  -- `LimbsRoom` and `LimbsFit`: one object's predicates
  let object (n : Name) : Name := n.modifyBase fun
    | .str pre s =>
      .str pre ((["Fit", "Room", "Bounds"].find? (s.endsWith ·)).elim s fun x =>
        String.ofList (s.toList.take (s.length - x.length)))
    | n => n
  let some cn := concl.getAppFn.constName? | return (`hfresh, none)
  for prem in prems do
    unless prem.getAppFn.constName?.map object == some (object cn) do
      continue
    let some m ← prem.getAppArgs.findM? fun a => return (← inferType a).isConstOf ``MemoryState
      | continue
    unless (← factPtr? prem) == some p do
      continue
    let atOld := prem.replace fun t => if t == m then some oldMem else none
    let some (.fvar h) := c.factMap[atOld]? | continue
    return (← h.getUserName, some h)
  let pred := (concl.getAppFn.constName?.map (·.getString!)).getD "fresh"
  let base := s!"h{pred.decapitalize}"
  return (← namedAfterPtr (.mkSimple base) p, none)

/-- The memory facts of the step's new state `new` (over the old state `S`), each `(h, motive)` with
`h : motive new`: a new block's size (`mlir_fresh`, at each write, carried up through the later
ones), every write an `mlir_read` lemma reads back, and every read fact of `S` the writes miss (the
others dropped, traced by `trace.rir`). Asserted in `g`; the old read facts, and the object facts a
fresh one supersedes, returned for clearing once the state is sealed, with the names the fresh ones
take over. Read through the writes while `S`'s facts hold. -/
def memFactsOf (g : MVarId) (S new : Expr) :
    MetaM (Array (FVarId × Expr) × Array FVarId × MVarId × Array Name) :=
  g.withContext do
    let newMem ← normWidths (← dsimpState (← mkAppM ``GlobalState.mem #[new]))
    let oldMem ← mkAppM ``GlobalState.mem #[S]
    let c ← MemCtx.build
    -- `(name, fact about newMem, proof)`, asserted last
    let mut facts : Array (Name × Expr × Expr) := #[]
    let mut superseded : Array FVarId := #[]
    -- a new block's size, a store's known bits, a started object's room: each `mlir_fresh`
    -- lemma's fact about a write (its first `MemoryState` argument), carried up to the new
    -- memory, unless a fact of the old one says as much and is carried (all but through a
    -- lifetime marker)
    let lifetime :=
      newMem.isAppOf ``MemoryState.lifetimeStart || newMem.isAppOf ``MemoryState.lifetimeEnd
    let layers ← freshLayers newMem
    let isMem (a : Expr) : MetaM Bool := return (← inferType a).isConstOf ``MemoryState
    -- each lemma with the head of its memory (`none`: any), so a write tries only its own
    let lemmas ←
      (← labelled `mlir_fresh).mapM fun n => do
          let (_, _, concl) ←
            forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels n))
          let m? ← concl.getAppArgs.findM? isMem
          return (n, m?.bind (·.getAppFn.constName?))
    let mut targets : Array Expr := #[]
    let mut layerFacts : Array (Expr × Expr) := #[]
    -- the objects a lifetime marker above a write starts or ends: no fact of the write survives
    let marked (i : Nat) (p : Expr) : Bool :=
      (layers.extract 0 i).any fun w =>
        let marker :=
          w.isAppOfArity ``MemoryState.lifetimeStart 2 || w.isAppOfArity ``MemoryState.lifetimeEnd 2
        marker && stripAdds w.appArg! == stripAdds p
    for i in [0:layers.size] do
      let wm := layers[i]!
      let head := wm.getAppFn.constName?
      -- an abbreviation's own head is no lemma's: all of them, unification unfolds it
      let abbrev_ ← head.elim (pure false) fun c => isReducible c
      for (n, h?) in lemmas do
        if !abbrev_ && h?.isSome && h? != head then
          continue
        let some (target, pf, name, old?, layerPf, concl) ←
          observing? do
              let lem ← mkConstWithFreshMVarLevels n
              let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
              let some m ← concl.getAppArgs.findM? isMem | failure
              unless ← withReducible (isDefEq m wm) do
                failure
              -- about `wm` as spelled, not the abbreviation's unfolding unification saw
              let mI ← instantiateMVars m
              let concl ← instantiateMVars concl
              let concl := if mI == wm then concl else concl.replace fun t =>
                if t == mI then some wm else none
              let concl ← normWidths concl
              let target :=
                if i == 0 then concl
                else mkAppN concl.getAppFn
                    (concl.getAppArgs.map fun a => if a == wm then newMem else a)
              if targets.contains target then
                failure
              if let some p ← factPtr? target then
                if marked i p then
                  failure
              if !lifetime then
                let atOld := target.replace fun t => if t == newMem then some oldMem else none
                if c.factMap.contains atOld then
                  failure
                if let some (k, _, p, w) := memPred? target then
                  for (_, ty) in c.facts do
                    let some (k', m', p', w') := memPred? ty | continue
                    if k ≤ k' && m' == oldMem && p' == p && (← normWidths w') == w then
                      failure
              -- premises about the memory below `wm`: as deep as its writes
              let fuel := max 4 (layers.size - i + 1)
              let mut prems := #[]
              for mv in ms do
                let mv := mv.mvarId!
                if !(← mv.isAssigned) && (← isProp (← mv.getType)) then
                  let ty ← instantiateMVars (← mv.getType)
                  prems := prems.push ty
                  -- a premise with an open value (a width): bound by the fact it matches
                  let some pf ←
                    if ty.hasExprMVar then
                      factMatching? c.facts ty
                    else
                      factDischarge c.toFactCtx fuel ty | failure
                  mv.assign pf
              unless ← ms.allM (·.mvarId!.isAssigned) do
                failure
              let pf := mkExpectedPropHint (← instantiateMVars (mkAppN lem ms)) concl
              let layerPf := pf
              -- up through the later writes, the fact at `wm` among the facts
              let pf ←
                if i == 0 then pure pf
                else
                  let fc := c.toFactCtx
                  let fc :=
                    { fc with facts := fc.facts.push (pf, concl),
                              factMap := fc.factMap.insert concl pf }
                  let some pf ← factDischarge fc (i + 2) target | failure
                  pure pf
              let (name, old?) ← freshName c target oldMem (← prems.mapM instantiateMVars)
              return (target, pf, name, old?, layerPf, concl) | continue
        targets := targets.push target
        facts := facts.push (name, target, pf)
        layerFacts := layerFacts.push (layerPf, concl)
        if let some h := old? then
          superseded := superseded.push h
    -- a masked store's known ranges, from the facts and those at the layers: where a literal
    -- mask is set (a global with undefined members), where a copy's source is known (`memcpy`)
    let lfacts := c.facts ++ layerFacts
    for i in [0:layers.size] do
      let wm := layers[i]!
      let_expr MemoryState.storeDef m' q v _ d := wm | continue
      let v ← normWidths v
      let mut cands : Array (Expr × Expr) := #[]
      if let some ⟨_, dv⟩ ← getBitVecValue? d then
        if let some n := v.nat? then
          -- the runs of set bits from a byte boundary
          let mut a := 0
          while a < n do
            if dv.getLsbD a && a % 8 == 0 then
              let mut b := a
              while b < n && dv.getLsbD b do
                b := b + 1
              let ptr ← if a == 0 then pure q else
                mkAppM ``Pointer.add #[q, mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64)
                  (mkNatLit (a / 8))]
              cands := cands.push (ptr, mkNatLit (b - a))
              a := b
            else
              a := a + 1
      else if let some src := (do
            let_expr MemoryState.definedAt m'' src _ := d | none
            guard (m'' == m'); some src) then
        for (_, ty) in c.facts do
          let some (2, mem, p', w') := memPred? ty | continue
          unless mem == m' do
            continue
          if p' == src then
            cands := cands.push (q, w')
          else if let some (src', off) := p'.app2? ``Pointer.add then
            if src' == src then
              cands := cands.push (← mkAppM ``Pointer.add #[q, off], w')
      for (ptr, w) in cands do
        let target ← mkAppM ``Fits #[newMem, ptr, w]
        if targets.contains target || marked i ptr then
          continue
        let some pf ← fitsProof? lfacts wm ptr w | continue
        let concl ← mkAppM ``Fits #[wm, ptr, w]
        let pf ←
          if i == 0 then pure pf
          else
            let fc := c.toFactCtx
            let fc :=
              { fc with facts := fc.facts.push (pf, concl), factMap := fc.factMap.insert concl pf }
            let some pf ← factDischarge fc (i + 2) target | continue
            pure pf
        targets := targets.push target
        facts := facts.push (← namedAfterPtr `hfits ptr, target, pf)
    let mut seen : Array Expr := #[]
    -- the writes read back: an `mlir_read` lemma's read of each write, at the new memory
    for w in layers do
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
        -- past the writes to the same read of `S`, with a fact: that fact is carried below, not
        -- read back (a stored value that is a read of `S` is read back)
        let v' ← normWidths v
        let below ← normWidths (e.replace fun t => if t == newMem then some oldMem else none)
        if v' == below && c.reads.contains v' then
          continue
        -- the value's own reads of `S` by `S`'s facts
        let r ← simpState v c
        let (v, pf) := (r.expr, ← mkEqTrans pf (← r.getProof))
        -- named after the pointer read, so facts at distinct pointers stay accessible
        -- (`q.add k` after `q` and `k`)
        let ptr? ←
          e.getAppArgs.findM? fun a => do
              return (← inferType a).isConstOf ``Pointer
        let name ← ptr?.elim (pure `hread) (namedAfterPtr `hread)
        -- read-backs at one pointer (an object's and its first field's): all but the last
        -- after their read
        facts :=
          facts.map fun (n, ty, pf) =>
            if n != name then (n, ty, pf)
            else
              let read := (ty.eq?.bind (·.2.1.getAppFn.constName?)).getD `read
              (n.appendAfter s!"_{read.getString!}", ty, pf)
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
    olds := olds ++ superseded.filter (!olds.contains ·)
    let renamed ← superseded.mapM (·.getUserName)
    -- each fact as `h : motive new`, `motive s` the fact with `s.mem` for the new memory
    let mut g := g
    let mut hyps := #[]
    for (name, ty, pf) in facts do
      let motive ← memMotive ty newMem
      let (h, g') ← (← g.assert name (motive.beta #[new]) pf).intro1P
      g := g'
      hyps := hyps.push (h, motive)
    return (hyps, olds, g, renamed)

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
      let (hyps, oldReads, g', _) ← memFactsOf g b s
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

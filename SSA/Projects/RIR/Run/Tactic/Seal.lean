module

public import SSA.Projects.RIR.Semantics.Env
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

/-- Exit and instructions in `block` from `pos` on. -/
def blockParts (block pos : Expr) : MetaM (Array Expr) := do
  let mut parts := #[← whnfD (← mkAppM ``BasicBlock.exit #[block])] -- Check all used in exit
  let mut rest :=
    ←
      whnfD
          (←
            mkAppM ``List.drop
                #[pos, (← mkAppM ``BasicBlock.body #[block])]) -- Ignore previous instructions
  while rest.isAppOfArity ``List.cons 3 do
    parts := parts.push rest.appFn!.appArg! -- `x` of `List.cons α x xs` (`x::xs`)
    rest ← whnfD rest.appArg! -- `xs`
  return parts

/-- The target blocks of the jumps in `exit`. -/
def jumpTargets (exit : Expr) : MetaM (Array Expr) := do
  let targets ← IO.mkRef #[]
  exit.forEachWhere (·.isAppOfArity ``Jump.mk 5) fun j => targets.modify (·.push (j.getArg! 3))
  targets.get

/-- The value registers some instruction or exit in `parts` reads. -/
def usedRegs (parts : Array Expr) : MetaM (Std.HashSet Nat) := do
  let regs ← IO.mkRef ({} : Std.HashSet Nat)
  for part in parts do
    part.forEachWhere (·.isAppOfArity ``Reg.val 4) fun reg => do
        if let some k← valRegIndex? reg then
          regs.modify (·.insert k)
  regs.get

/-- The value registers `parts` (an exit, then instructions in order) reads before writing them;
`defined` are written on entry (a block's parameters). A register a loop body rewrites before
reading it is not live into the body. -/
def exposedRegs (parts : Array Expr) (defined : Std.HashSet Nat := {}) : MetaM (Std.HashSet Nat) :=
  do
  let mut defined := defined
  let mut regs : Std.HashSet Nat := {}
  for part in parts.extract 1 parts.size |>.push parts[0]! do
    for k in ← usedRegs #[part] do
      unless defined.contains k do
        regs := regs.insert k
    let writes ← IO.mkRef #[]
    part.forEachWhere (·.isAppOfArity ``Dst.mk 4) fun d => writes.modify (·.push (d.getArg! 2))
    for i in ← writes.get do
      if let some k← finNLit? i then
        defined := defined.insert k
  return regs

/-- The value registers block `t`'s parameters write on entry. -/
def paramRegs (func t : Expr) : MetaM (Std.HashSet Nat) := do
  let params ← whnfD (mkApp2 (mkConst ``Func.blockParams) func t)
  let regs ← IO.mkRef ({} : Std.HashSet Nat)
  params.forEachWhere (·.isAppOfArity ``Dst.mk 4) fun d => do
      if let some k← finNLit? (d.getArg! 2) then
        regs.modify (·.insert k)
  regs.get

/-- A function's block `k`: its registers read and its jump targets. Each step asks again for the
same reachable blocks. -/
initialize blockUseCache : IO.Ref (Std.HashMap (Expr × Nat) (Std.HashSet Nat × Array Expr)) ←
  IO.mkRef {}

/-- A closed block's registers read before written from each position on (its exit included),
by position: each step asks for the next, and walking the instruction list again per step is
quadratic in the block's length. -/
initialize blockSuffixCache : IO.Ref (Std.HashMap Expr (Array (Std.HashSet Nat))) ← IO.mkRef {}

/-- `exposedRegs (blockParts block pos)` for every `pos`, last position (the exit alone) last. -/
def suffixExposed (block : Expr) : MetaM (Array (Std.HashSet Nat)) := do
  if let some r := (← blockSuffixCache.get)[block]? then
    return r
  let parts ← blockParts block (mkNatLit 0)
  let n := parts.size - 1
  let mut cur ← usedRegs #[parts[0]!]
  let mut out := Array.replicate (n + 1) cur
  for j in [0:n] do
    let i := n - 1 - j
    let part := parts[i + 1]!
    let writes ← IO.mkRef #[]
    part.forEachWhere (·.isAppOfArity ``Dst.mk 4) fun d => writes.modify (·.push (d.getArg! 2))
    for w in ← writes.get do
      if let some k← finNLit? w then
        cur := cur.erase k
    cur := cur.union (← usedRegs #[part])
    out := out.set! i cur
  blockSuffixCache.modify (·.insert block out)
  return out

def liveRegs (func block pos : Expr) : MetaM (Std.HashSet Nat) := do
  let block ← instantiateMVars block
  let pos ← instantiateMVars pos
  -- a closed block at a literal position: its suffixes once
  let cached? ←
    if block.hasFVar || block.hasMVar then
      pure none
    else
      match pos.nat? <|> pos.rawNatLit? with
      | some i =>
        do
          let sx ← suffixExposed block
          pure (sx[i]?)
      | none =>
        pure none
  let exit ← whnfD (← mkAppM ``BasicBlock.exit #[block])
  let mut live ←
    match cached? with
    | some regs =>
      pure regs
    | none =>
      exposedRegs (← blockParts block pos)
  let mut todo ← jumpTargets exit
  let mut seen : Std.HashSet Nat := {}
  let func ← instantiateMVars func
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    let some k ← finNLit? t | throwError "non-literal jump target {t}"
    if seen.contains k then
      continue
    seen := seen.insert k
    let (regs, targets) ←
      match (← blockUseCache.get)[(func, k)]? with
      | some r =>
        pure r
      | none =>
        do
          let ps ← blockParts (mkApp2 (mkConst ``Func.blocks) func t) (mkNatLit 0)
          let r := (← exposedRegs ps (← paramRegs func t), ← jumpTargets ps[0]!)
          blockUseCache.modify (·.insert (func, k) r)
          pure r
    live := live.union regs
    todo := todo ++ targets
  return live

/-- One `Env.write` of a chain. -/
structure ChainWrite where
  dst : Expr
  val : Expr
  idx : Nat

/-- Split `base[d₀ := v₀, …]` into `base` and its writes, bottom first. -/
partial def splitChain (e : Expr) : MetaM (Expr × Array ChainWrite) := do
  let_expr Env.write _ _ base dst val := e | return (e, #[])
  let some idx ← dstIndex? dst | throwError "non-literal destination {dst}"
  let (b, ws) ← splitChain base
  return (b, ws.push ⟨dst, val, idx⟩)

/-- `env.write w.dst w.val` -/
def ChainWrite.apply (w : ChainWrite) (env : Expr) : MetaM Expr :=
  mkAppM ``Env.write #[env, w.dst, w.val]

def chainFn (ws : List ChainWrite) (env : Expr) : MetaM Expr := do
  withLocalDeclD `e (← inferType env) fun e => do
      let body ←
        ws.foldlM
            (fun acc w => do
              w.apply acc)
            e
      mkLambdaFVars #[e] body

/-- Apply `Env.writeComm` to `e`, provign `h` by `decide` -/
private def writeComm (e : Expr) : MetaM Expr := do
  let lem ← mkConstWithFreshMVarLevels ``Env.write_comm
  let (args, _, ty) ← forallMetaTelescopeReducing (← inferType lem)
  let some (_, lhs, _) := ty.eq? | throwError "`write_comm` is not an equation"
  unless ← withReducible (isDefEq lhs e) do
    throwError "not two writes:{indentExpr e}"
  let h := args.back!
  h.mvarId!.assign (← mkDecideProof (← instantiateMVars (← inferType h)))
  instantiateMVars (mkAppN lem args)

/-- `incoming` written over `env` swapped below the live writes `env` ends with. -/
private def swapN (env : Expr) (incoming : ChainWrite) : (liveWrites : List ChainWrite) → MetaM Expr
  | [] => do
    mkEqRefl (← incoming.apply env)
  | w :: ws => do
    let outerSwap ← writeComm (← incoming.apply env)
    let_expr Env.write _ _ innerBase _ _ := env | throwError m!"{env} is no env write"
    let innerSwaps ← swapN innerBase incoming ws
    mkEqTrans outerSwap (← mkCongrArg (← chainFn [w] env) innerSwaps)

/-- `env` with the writes `remaining` (each with its position in the chain) equal to it with the
`dead` ones first, the live ones last; `writtenLive` the live writes over `env`, outermost first. A
dead write never passes one to its register: those below it are dead too. -/
private def partitionProof (env : Expr) (dead : Nat → Bool) (writtenLive : List ChainWrite) :
    (remaining : List (ChainWrite × Nat)) → MetaM Expr
  | [] => do
    mkEqRefl env
  | (w, i) :: ws =>
    if !dead i then do
      partitionProof (← w.apply env) dead (w :: writtenLive) ws
    else do
      let swapProof ← swapN env w writtenLive
      let some (_, _, rhs) :=
        (← inferType swapProof).eq? | throwError "swap proof is not an equation"
      let partProof ← partitionProof rhs dead writtenLive ws
      -- the swap lifted to the remaining writes
      let lifted ← mkCongrArg (← chainFn (ws.map (·.1)) env) swapProof
      mkEqTrans lifted partProof

/-- Clear a value `x` and its hyp `hx : x = _` if possible -/
def tryClearValue (g : MVarId) (v : FVarId) : MetaM MVarId :=
  g.withContext do
    let some hyp ← observing? (findEqWithLhs? (.fvar v)) | return g
    let some hyp := hyp | return g
    return (←
            observing? do
                (← g.clear hyp).clear v).getD
        g

/-- Clear each `v` with `hv : v = _` that nothing but `hv` mentions, until nothing changes. -/
def clearUnusedValues (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let decls := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
    -- per local: how many other locals, or the goal, mention it; and its defining `hv`
    let mut uses : Std.HashMap FVarId Nat := {}
    let mut defs : Array (FVarId × FVarId × Array FVarId) := #[]
    for d in decls do
      let ty ← instantiateMVars d.type
      let xs := (collectFVars {} ty).fvarIds
      for x in xs do
        uses := uses.alter x (some <| ·.getD 0 + 1)
      if let some (_, .fvar v, _) := ty.consumeMData.eq? then
        unless ← isProp (← v.getType) do
          defs := defs.push (v, d.fvarId, xs)
    for x in (collectFVars {} (← instantiateMVars (← g.getType))).fvarIds do
      uses := uses.alter x (some <| ·.getD 0 + 1)
    -- later values first: clearing `hv21` can drop `v20` to its `hv20` alone
    let mut g := g
    for (v, hv, xs) in defs.reverse do
      unless uses.getD v 0 == 1 do
        continue
      let some g' ←
        observing?
            (do
              (← g.clear hv).clear v) | continue
      g := g'
      for x in xs do
        uses := uses.modify x (· - 1)
    return g

/-- Whether the fact `ty` about the root `E₀` also holds of `E₀` after writes to `dead`, by
definition: a read of an argument or of a value register no dead write touches, or `E₀.args`. -/
def carriesOver (E₀ : Expr) (dead : Std.HashSet Nat) (ty : Expr) : MetaM Bool := do
  let some (_, lhs, rhs) := ty.eq? | return false
  if rhs.containsFVar E₀.fvarId! then
    return false
  match_expr lhs with
  | Env.args _ e =>
    return e == E₀
  | Env.read _ _ e reg =>
    unless e == E₀ do
      return false
    if reg.isAppOf ``Reg.arg then
      return true
    let some k ← valRegIndex? reg | return false
    return !dead.contains k
  | _ =>
    return false

def runSeal : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    let some hE ← findLocalEq? runBodyFrom.env | return
    let (hE, E₀chain) := (hE.decl.fvarId, hE.rhs)
    -- the function, for the blocks after this one: `Func.continue`'s first argument
    -- without `Func.continue` (a lemma about a bare `runBodyFrom`), liveness is unknown: keep all
    let some cont := goal.find? (·.isAppOf ``Func.continue) | return
    let liveRegs ← liveRegs (cont.getArg! 0) runBodyFrom.block runBodyFrom.idx
    let (E₀, chain) ← splitChain E₀chain
    -- dead: not read later, or written again higher in the chain (a loop's next iteration)
    let idxs := chain.map (·.idx)
    let shadowed (i : Nat) := idxs.extract (i + 1) idxs.size |>.contains idxs[i]!
    let isDead (shadow : Bool) (i : Nat) := idxs[i]! ∉ liveRegs || shadow && shadowed i
    -- the root's facts (a block lemma's inputs) carry over to the sealed root; any other mention (a
    -- loop's continuation) keeps the root. A fact about a shadowed write's register keeps it.
    let rootFacts ←
      if E₀.isFVar then
        (← hypsMentioning E₀ (except := #[hE])).mapM fun h => do
            let d ← h.getDecl
            return (d.fvarId, d.userName, ← instantiateMVars d.type)
      else
        pure #[]
    let carries (shadow : Bool) : MetaM Bool := do
      let dead : Std.HashSet Nat :=
        (List.range idxs.size).foldl (fun s i => if isDead shadow i then s.insert idxs[i]! else s)
          {}
      rootFacts.allM fun (_, _, ty) => carriesOver E₀ dead ty
    let shadow ← carries true
    unless shadow || (← carries false) do
      return
    let deadWrites := chain.toList.zipIdx.filter (isDead shadow ·.2) |>.map (·.1)
    let E₀' := (← chainFn deadWrites E₀).beta #[E₀]
    let mut carried : Array (FVarId × Name × Expr) :=
      rootFacts.map fun (h, n, ty) => (h, n, ty.replaceFVar E₀ E₀')
    let partitionProof ← partitionProof E₀ (isDead shadow) [] (chain.toList.zipIdx)
    let hE' ← mkEqTrans (.fvar hE) partitionProof
    let r ← g.assertAfter hE `hE (← inferType hE') hE'
    -- `assertAfter` reintroduces the locals after `hE`: the carried facts by their new ids
    carried := carried.map fun (h, n, ty) => ((r.subst.get h).fvarId!, n, r.subst.apply ty)
    let mut g ← r.mvarId.clear hE
    let (facts, g') ←
      g.assertHypotheses
          (carried.map fun (h, n, ty) =>
            { userName := n, type := ty, value := mkExpectedPropHint (.fvar h) ty })
    g := g'
    for (h, _, _) in carried do
      g ← g.clear h
    let (_, g') ← generalizeOpaque g (hyps := #[r.fvarId] ++ facts) E₀' `E₀ #[]
    -- the old root, now unused, if a local
    g ←
      if E₀.isFVar then
        g'.clear E₀.fvarId!
      else
        pure g'
    -- the values only their own `hv` mentions, the dead writes' among them
    replaceMainGoal [← clearUnusedValues g]

elab "seal" : tactic => runSeal

end

end LeanMLIR.RIR

module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.Tactic.Parse
public meta import Lean.Elab.Tactic

namespace LeanMLIR.RIR.Tactic

open Lean Elab Tactic Meta

public meta section

structure GeneralizeFact where
  /-- Name of the fact -/
  name : Name
  /-- Generate the fact's statement from the abstracted variable -/
  mkType : Expr → MetaM Expr
  /-- Proof of `mkType (generalized expression)` -/
  proof : Expr

/-- Generalize `e` in the goal `g` and hyps `hyps` to a fresh opaque local `xName`.
`facts` specifies the hypotheses to generate from the generalization. -/
def generalizeOpaque (g : MVarId) (e : Expr) (xName : Name) (facts : Array GeneralizeFact)
    (hyps : Array FVarId := #[]) : MetaM (Array FVarId × MVarId) := do
  let (reverted, g) ← g.revert (preserveOrder := true) hyps
  g.withContext do
      let ty ← inferType e -- Type of the expression to generalize
      -- reducible: `e` occurs verbatim, and default transparency unfolds every `Env.write`
      let tgtAbstract ← withReducible <| kabstract (← instantiateMVars (← g.getType)) e
      -- the new goal under binders for `x` and the facts, applied to `e` and the proofs: the value
      -- stays at this one place, where an `intro`ed goal would have it substituted into every later
      -- step on instantiation
      let (fvs, gNew) ←
        withLocalDeclD xName ty fun x => do
            let rec withFacts (i : Nat) (hs : Array Expr) : MetaM (Array FVarId × MVarId) := do
              if h : i < facts.size then
                withLocalDeclD facts[i].name (← facts[i].mkType x) fun hx =>
                    withFacts (i + 1) (hs.push hx)
              else
                let body ←
                  mkFreshExprSyntheticOpaqueMVar (tgtAbstract.instantiate1 x) (tag := ← g.getTag)
                let lam ← mkLambdaFVars (#[x] ++ hs) body
                g.assign (mkAppN lam (#[e] ++ facts.map (·.proof)))
                return ((#[x] ++ hs).map (·.fvarId!), body.mvarId!)
            withFacts 0 #[]
      let g := gNew
      let (_, g) ← g.introNP reverted.size -- Revert reverting
      return (fvs, g)

/-- The `Nat` behind a `Dst`'s index, when it is a literal. -/
def dstIndex? (d : Expr) : MetaM (Option Nat) := do
  let i ← whnf (← mkAppM ``Dst.i #[d])
  (Meta.evalNat (← whnf (← mkAppM ``Fin.val #[i]))).run

/-- Replace the body index by its `Nat` literal: `0 + 1 + 1` becomes `2`. -/
def reduceIndex (g : MVarId) : MetaM MVarId :=
  g.withContext do
    let goal ← instantiateMVars (← g.getType)
    let idx := (← getRunBodyFrom goal).idx
    -- `pos + 1 + 1` to `pos + 2`, as pattern lemmas state their continuations; else a literal
    let lit ←
      match ← (Meta.evalNat idx).run with
      | some literal =>
        pure (mkNatLit literal)
      | none =>
        do
          let mut base := idx
          let mut k := 0
          while true do
            let_expr HAdd.hAdd _ _ _ _ a b := base | break
            let some n ← (Meta.evalNat b).run | break
            base := a
            k := k + n
          if k ≤ 1 then
            return g
          mkAppM ``HAdd.hAdd #[base, mkNatLit k]
    if lit == idx then
      return g
    g.replaceTargetDefEq ((← kabstract goal idx).instantiate1 lit)

def finNLit? (n : Expr) : MetaM (Option Nat) := do
  if let some k← (Meta.evalNat (← mkAppM ``Fin.val #[n])).run then
    return k
  let_expr OfNat.ofNat _ n _ := n | return none
  return n.rawNatLit?

/-- The literal index of a `Reg.val k h`, if it has one. -/
def valRegIndex? (r : Expr) : MetaM (Option Nat) := do
  let_expr Reg.val _ _ i _ := r | return none
  finNLit? i

/-- Replace `e` in `m`'s target by `r.expr`, using the proof `e = r.expr` from `r`. -/
def replaceBySimp (m : MVarId) (e : Expr) (r : Simp.Result) : MetaM MVarId := do
  -- reducible: `e` occurs verbatim, and a default-transparency mismatch against a similar value
  -- (`(f x).1` against `(f x).2`) unfolds `f` before failing
  let body ← withReducible <| kabstract (← instantiateMVars (← m.getType)) e
  let motive := Expr.lam `val (← inferType e) body .default -- As a lambda
  let simpProof ← r.getProof' e
  let mvarProof ← mkCongrArg motive simpProof
  let newMVar := body.instantiate1 r.expr
  m.replaceTargetEq newMVar mvarProof -- Using congruence, get proof over goal

/-- Whether `ty` is a continuation: a fact about a function's run (`Func.ContAt`, `∀ E', … runFrom
… = K`), which stays about its own state. -/
def isContinuation (ty : Expr) : MetaM Bool :=
  return ((← whnfR ty).find? (·.isAppOf ``Func.runFrom)).isSome

/-- `p` by `decide`, when it evaluates to `true`. -/
def decideProof? (p : Expr) : MetaM (Option Expr) := do
  let .some inst ← trySynthInstance (mkApp (mkConst ``Decidable) p) | return none
  unless
    (← withDefault <| whnf (mkApp2 (mkConst ``Decidable.decide) p inst)).isConstOf ``Bool.true do
    return none
  return some (← mkDecideProof p)

/-- `fun y : ty => e` with each `t` in `e` replaced by `f y`. -/
def motiveOver (e t ty : Expr) (f : Expr → Expr := id) : MetaM Expr :=
  withLocalDeclD `y ty fun y =>
    mkLambdaFVars #[y] (e.replace fun s => if s == t then some (f y) else none)

/-- `a ≠ b`, maybe an `autoParam`, or `¬a = b`: `(a, b)`. -/
def neSides? (ty : Expr) : Option (Expr × Expr) :=
  let ty := ty.cleanupAnnotations
  match ty.ne? with
  | some (_, a, b) => some (a, b)
  | none => ty.not?.bind (·.eq?) |>.map fun (_, a, b) => (a, b)

/-- A goal `a ∧ b` closed by `And.intro` of two new goals, returned. -/
def splitAnd? (g : MVarId) (ty : Expr) : MetaM (Option (MVarId × MVarId)) := do
  let some (a, b) := ty.and? | return none
  let ga ← g.withContext (mkFreshExprSyntheticOpaqueMVar a)
  let gb ← g.withContext (mkFreshExprSyntheticOpaqueMVar b)
  g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
  return some (ga.mvarId!, gb.mvarId!)

/-- The simp sets `sets`, after `extra`, as one context. -/
def simpSetContext (sets : Array Name) (extra : Array SimpTheorems := #[]) : MetaM Simp.Context :=
  do
  let thms ←
    sets.mapM fun n => do
        let some ext ← getSimpExtension? n | throwError "no `{n}` simp set"
        ext.getTheorems
  Simp.mkContext (simpTheorems := extra ++ thms) (congrTheorems := ← getSimpCongrTheorems)

/-- The hypotheses whose statement mentions `e`, except `except`. -/
def hypsMentioning (e : Expr) (except : Array FVarId := #[]) : MetaM (Array FVarId) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail || except.contains d.fvarId then
        return acc
      return if e.occurs (← instantiateMVars d.type) then acc.push d.fvarId else acc

/-- The unique equation `_ : lhs = _`, if there is one; `what` names it in errors. -/
def findLocalEq? (lhs : Expr) (what : MessageData := m!"`{lhs} = _`") : MetaM (Option LocalEq) := do
  match (← localEqs).filter (·.lhs == lhs) with
  | #[] =>
    return none
  | #[e] =>
    return some e
  | es =>
    throwError "ambiguous: {es.size} hypotheses {what}"

/-- The unique hypothesis `_ : lhs = _`, if there is one. -/
def findEqWithLhs? (lhs : Expr) (what : MessageData := m!"`{lhs} = _`") : MetaM (Option FVarId) :=
  do
  return (← findLocalEq? lhs what).map (·.decl.fvarId)

/-- The unique hypothesis `_ : lhs = _`. -/
def findEqWithLhs (lhs : Expr) (what : MessageData := m!"`{lhs} = _`") : MetaM FVarId := do
  let h ← findEqWithLhs? lhs what
  let some (h) := h | throwError "no hypothesis {what}"
  return h

/-- `a ≠ b` from `h : [...].Nodup`, when `a` and `b` are among the list's elements. -/
def nodupNe? (h ty a b : Expr) : MetaM (Option Expr) := do
  let_expr List.Nodup _ l := ty | return none
  -- a literal of more than 32 elements elaborates with `let`s
  let some xs := (← zetaReduce l).listLit? |>.map (·.2) | return none
  let idx (e : Expr) : MetaM (Option Nat) := do
    for x in xs, k in [0:xs.length] do
      if ← withReducible (isDefEq e x) then
        return some k
    return none
  let some i ← idx a | return none
  let some j ← idx b | return none
  let lt (m n : Expr) :=
    mkDecideProof (mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) m n)
  let len ← mkAppM ``List.length #[l]
  let ne (i j : Nat) := do
    mkAppM ``List.Nodup.getElem_ne #[h, ← lt (mkNatLit i) (mkNatLit j), ← lt (mkNatLit j) len]
  if i < j then
    return some (← ne i j)
  if j < i then
    return some (← mkAppM ``Ne.symm #[← ne j i])
  return none

/-- The tag on the equation `hx : x = _` of a step value named with `with`. -/
def namedTag : Name :=
  `rir_named

/-- `ty`, the equation of a step value named with `with`, tagged so: such a value stays folded where
the state takes it. -/
def tagNamed (ty : Expr) : Expr :=
  mkMData (KVMap.empty.insert namedTag (.ofBool true)) ty

/-- Whether `ty` is a named value's equation (`tagNamed`). -/
def isNamedEq (ty : Expr) : Bool :=
  match ty with
  | .mdata d _ => d.getBool namedTag
  | _ => false

end

end LeanMLIR.RIR.Tactic

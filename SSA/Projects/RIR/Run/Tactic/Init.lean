module

public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.Run.Call
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Parse
public meta import SSA.Projects.RIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

section FuncInit

elab "extract_state" : tactic => do
  let (g, goal) ← getGoalType
  let runFrom ← getFuncRunFromGoal goal
  let (fvs, g) ←
    g.withContext do
        generalizeOpaque g (hyps := ← hypsMentioning runFrom.state) runFrom.state `S₀
            #[⟨`hS₀, (mkEq · runFrom.state), ← mkEqRefl runFrom.state⟩]
  let S₀ := mkFVar fvs[0]!
  let hS₀ := fvs[1]!
  let stateHyps ←
    g.withContext do
        hypsMentioning S₀ (except := #[hS₀])
  let (reverted, g) ← g.revert stateHyps (preserveOrder := true)
  let g ←
    g.withContext do
        let goalType ← instantiateMVars (← g.getType)
        let target := (← getFuncRunFromGoal goalType).app
        let tyNew ←
          withLocalDeclD `S (← inferType S₀) fun S => do
              let rec go : Nat → Expr → Expr
                | n + 1, .forallE nm d b i => .forallE nm (d.replaceFVar S₀ S) (go n b) i
                | _, e =>
                  e.replace (fun t => if t == target then some (mkApp target.appFn! S) else none)
              withLocalDeclD `hS (← mkEq S S₀) fun hS =>
                  mkForallFVars #[S, hS] (go reverted.size goalType)
        let gNew ← mkFreshExprSyntheticOpaqueMVar tyNew (tag := ← g.getTag)
        g.assign (mkAppN gNew #[S₀, ← mkEqRefl S₀])
        let (_, g) ← gNew.mvarId!.introNP (2 + reverted.size)
        pure g
  let g ← g.clear hS₀
  replaceMainGoal [g]
  if let some fs := runFrom.state.fvarId? then
    replaceMainGoal [← g.clear fs]

elab "extract_env" : tactic => do
  let (g, goal) ← getGoalType
  let runFrom ← getFuncRunFromGoal goal
  let rhs := runFrom.env.appArg!
  let stmt (x : Expr) : MetaM Expr := do
    mkEq (← mkAppM ``Env.args #[x]) rhs
  let (fvs, g) ←
    g.withContext do
        -- We abstract `E₀` from `Env.init args` and
        -- want `hE₀args : E₀.args = args`
        unless runFrom.env.isAppOfArity ``Env.init 2 do
          throwTacticEx `extract_env g
              m!"Expected env {runFrom.env} to be an application of {``Env.init}"
        let proof := mkExpectedPropHint (← mkEqRefl rhs) (← stmt runFrom.env)
        let fact := ⟨`hE₀args, stmt, proof⟩
        generalizeOpaque g runFrom.env `E₀ #[fact]
  let E₀ := mkFVar fvs[0]!
  let hE₀args' := fvs[1]!
  let hE₀args := mkFVar hE₀args'
  let (_, g) ←
    g.withContext do
        generalizeOpaque g E₀ `E #[⟨`hE, (mkEq · E₀), ← mkEqRefl E₀⟩, ⟨`hEargs, stmt, hE₀args⟩]
  let g ← g.clear hE₀args'
  replaceMainGoal [g]

/-- With the initial state `S₀` (`hS : S = S₀`), `hwf : S.WF` and each `h : Fits S.mem p w` also
about `S₀` (`hwf₀`, `h₀`): the steps carry only facts of the current state, and reads through `hS`
below a frame's new blocks, like removing the frame at the end, need the initial ones. -/
meta def addInitialFacts : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let S := (← getFuncRunFromGoal goal).state
    let hS ← findEqWithLhs S
    let mut facts := #[]
    for h in ← hypsMentioning S (except := #[hS]) do
      let d ← h.getDecl
      let ty ← instantiateMVars d.type
      unless ty.isAppOfArity ``GlobalState.WF 1 || ty.isAppOfArity ``Fits 3 do
        continue
      let motive := .lam `s (← inferType S) (← kabstract ty S) .default
      let pf ← mkEqNDRec motive d.toExpr (mkFVar hS)
      facts :=
        facts.push { userName := d.userName.appendAfter "₀", type := ← inferType pf, value := pf }
    let (_, g) ← g.assertHypotheses facts
    replaceMainGoal [g]

/-- Start a proof of `f.call args s = .value (r, t)`: for a frame-free `f`, reduce it to `f.run` by
`Func.call_eq_of_run_eq` (`t.WF` by `simp [mlir_mem, *]`, `t.alloc = s.alloc` by `rfl`), else to
`f.run` followed by the frame erase (`Func.call_eq_run_bind`). Then go to the entry block's
`runFrom`, and extract the state and env. -/
elab "func_init" : tactic =>
  withMainContext do
    let (_, goal) ← getGoalType
    unless (goal.find? (·.isAppOf ``Func.call)).isSome do
      throwError "`func_init` expects a goal `f.call args s = _`, got{indentExpr goal}"
    -- a frame-free function's `call` is its `run`; otherwise `run`, then the frame erase
    let framed ←
      (do
            evalTactic
                (←
                  `(tactic|
                      refine
                        Func.call_eq_of_run_eq ?_ (by simp [$(mkIdent `mlir_mem):ident, *]) rfl))
            pure false) <|>
          (do
            evalTactic (← `(tactic| rw [Func.call_eq_run_bind]));
            pure true)
    let (g, goal) ← getGoalType
    let r ← g.rewrite goal (← mkConstWithFreshMVarLevels ``Func.run_runFrom_eq)
    replaceMainGoal ((← g.replaceTargetEq r.eNew r.eqProof) :: r.mvarIds)
    evalTactic (← `(tactic | extract_state))
    evalTactic (← `(tactic | extract_env))
    if framed then
      addInitialFacts

end FuncInit

section BlockInit

/-- `e` with reducible definitions unfolded at its head and at its write chain's root. -/
meta partial def unfoldEnvChain (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  let_expr Env.write Γ t base dst val := e | return e
  return mkAppN e.getAppFn #[Γ, t, ← unfoldEnvChain base, dst, val]

/-- Unfold reducible definitions at the head of the block's env (a named loop-header env) and at
its write chain's root (`(hdr E)[%k := v]`), so the steps see its writes. -/
meta def unfoldEnvHead : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let env := (← getRunBodyFrom goal).env
    let env' ← unfoldEnvChain env
    unless env' == env do
      replaceMainGoal
          [← g.replaceTargetDefEq (goal.replace fun e => if e == env then env' else none)]

elab "block_init" : tactic => do
  evalTactic
      (←
        `(tactic|
            ( rw [Func.runFrom_eq]
              rw [BasicBlock.run_eq]
              simp only [EffectM.bind_eq, EffectM.map_eq, bind_assoc, bind_map_left])))
  try
    unfoldEnvHead
  catch _ =>
    pure ()

end BlockInit

end LeanMLIR.RIR

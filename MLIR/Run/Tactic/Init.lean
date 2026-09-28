module

public import MLIR.Semantics.Func
public import MLIR.Run.Call
public meta import MLIR.Run.BasicBlock
public meta import MLIR.Run.Tactic.Parse
public meta import MLIR.Run.Tactic.Util
public meta import Lean.Elab.Tactic
public import MLIR.Run.Tactic.Trace

namespace MLIR

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
        generalizeOpaque g (hyps := #[]) runFrom.env `E₀ #[fact]
  let E₀ := mkFVar fvs[0]!
  let hE₀args' := fvs[1]!
  let hE₀args := mkFVar hE₀args'
  let (_, g) ←
    g.withContext do
        generalizeOpaque g (hyps := #[]) E₀ `E
            #[⟨`hE, (mkEq · E₀), ← mkEqRefl E₀⟩, ⟨`hEargs, stmt, hE₀args⟩]
  let g ← g.clear hE₀args'
  replaceMainGoal [g]

/-- With the initial state `S₀` (`hS : S = S₀`) and `hwf : S.WF`, add `hwf₀ : S₀.WF`: the steps only
carry `WF` of the current state, and removing the frame at the end needs the initial one. -/
meta def addInitialWF : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let S := (← getFuncRunFromGoal goal).state
    let hS ← findEqWithLhs S m!"`{S} = _`"
    let wfTy ← mkAppM ``GlobalState.WF #[S]
    let some hwf ←
      (← getLCtx).findDeclM? fun d => do
          if !d.isImplementationDetail && (← withReducible (isDefEq d.type wfTy)) then
            return some d
          return none | return
    let motive ←
      withLocalDeclD `x (mkConst ``GlobalState) fun x => do
          mkLambdaFVars #[x] (← mkAppM ``GlobalState.WF #[x])
    let hwf₀ ← mkEqNDRec motive hwf.toExpr (mkFVar hS)
    let (_, g) ←
      g.assertHypotheses
          #[{ userName := hwf.userName.appendAfter "₀", type := ← inferType hwf₀, value := hwf₀ }]
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
      addInitialWF

end FuncInit

section BlockInit

macro "block_init" : tactic =>
  `(tactic | (
    rw [Func.runFrom_eq]
    rw [BasicBlock.run_eq]
    simp only [EffectM.bind_eq, EffectM.map_eq, bind_assoc, bind_map_left]
  ))

end BlockInit

end MLIR

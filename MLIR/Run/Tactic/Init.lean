module

public import MLIR.Semantics.Func
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
  let (_, g) ←
    g.withContext do
        generalizeOpaque g (hyps := ← hypsMentioning S₀ (except := #[hS₀])) S₀ `S
            #[⟨`hS, (mkEq · S₀), ← mkEqRefl S₀⟩]
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

elab "func_init" : tactic =>
  withMainContext do
    let (g, goal) ← getGoalType
    let r ← g.rewrite goal (← mkConstWithFreshMVarLevels ``Func.run_runFrom_eq)
    replaceMainGoal ((← g.replaceTargetEq r.eNew r.eqProof) :: r.mvarIds)
    evalTactic (← `(tactic | extract_state))
    evalTactic (← `(tactic | extract_env))

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

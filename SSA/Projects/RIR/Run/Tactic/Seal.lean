module

public import SSA.Projects.RIR.Semantics.Env
public meta import SSA.Projects.RIR.Run.BasicBlock
public meta import SSA.Projects.RIR.Run.Tactic.Env
public meta import Lean.Elab.Tactic
public import SSA.Projects.RIR.Run.Tactic.Trace

namespace LeanMLIR.RIR

open Lean Elab Tactic Meta

public meta section

/-- The literal index of a `Reg.val k h`, if it has one. -/
def valRegIndex? (r : Expr) : MetaM (Option Nat) := do
  let_expr Reg.val _ _ i _ := r | return none
  finNLit? i

def liveRegs (block pos : Expr) : MetaM (Std.HashSet Nat) := do
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
  -- We now collected all expressions
  let regs ← IO.mkRef ({} : Std.HashSet Nat)
  for part in parts do
    part.forEachWhere (·.isAppOfArity ``Reg.val 4) fun reg => do
        if let some k← valRegIndex? reg then
          regs.modify (·.insert k)
  return (← regs.get)

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

/-- `fun e => e.write w.dst w.val`, for `mkCongrArg`. -/
def ChainWrite.fn (w : ChainWrite) (env : Expr) : MetaM Expr := do
  withLocalDeclD `e (← inferType env) fun e => do
      mkLambdaFVars #[e] (← w.apply e)

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
  unless ← isDefEq lhs e do
    throwError "not two writes:{indentExpr e}"
  let h := args.back!
  h.mvarId!.assign (← mkDecideProof (← instantiateMVars (← inferType h)))
  instantiateMVars (mkAppN lem args)

private def swapN (env : Expr) (incoming : ChainWrite) :
    Nat → (liveWrites : List ChainWrite) → MetaM Expr
  | 0, [] => do
    let write ← incoming.apply env
    mkEqRefl write
  | n + 1, w :: ws => do
    let outerWrite ← incoming.apply env
    let outerSwap ← writeComm outerWrite
    let_expr Env.write _ _ innerBase _ _ := env | throwError m!"{env} is no env write"
    let innerSwaps ← swapN (innerBase) incoming n ws
    let innerSwapsCongr ← mkCongrArg (← w.fn env) innerSwaps
    mkEqTrans outerSwap innerSwapsCongr
  | n, ws => do
    throwError m!"Mismatch between N ({n}) and write length ({ws.length})"

private def partitionProof' (env : Expr) (live : Std.HashSet Nat) (liveCount : Nat)
    (writtenLive : List ChainWrite /-`head` is the most outer write-/ ) :
    (remainingWrites : List ChainWrite) → MetaM Expr
  | [] => do
    mkEqRefl env
  | w :: ws =>
    if w.idx ∈ live then do
      partitionProof' (← w.apply env) live (liveCount + 1) (w :: writtenLive) ws
    else do
      let swapProof ← swapN env w liveCount writtenLive
      let some (_, _, rhs) :=
        (← inferType swapProof).eq? | throwError "swap proof is not an equation"
      let partProof ← partitionProof' rhs live liveCount writtenLive ws
      let lifted ←
        mkCongrArg (← chainFn ws env) swapProof -- Lift the swap proof to the remaining writes
      mkEqTrans lifted partProof

private def partitionProof (live : Std.HashSet Nat) (env : Expr) (writes : Array ChainWrite) :=
  partitionProof' env live 0 [] writes.toList

def runSeal : TacticM Unit :=
  withMainContext do
    let (g, goal) ← getGoalType
    let runBodyFrom ← getRunBodyFrom goal
    let hE ← findEqWithLhs runBodyFrom.env m!"`{runBodyFrom.env} = _`"
    let some (_, _, E₀chain) :=
      (← inferType (.fvar hE)).eq? | throwError "swap proof is not an equation"
    let liveRegs ← liveRegs runBodyFrom.block runBodyFrom.idx
    let (E₀, chain) ← splitChain E₀chain
    let partitionProof ← partitionProof liveRegs E₀ chain
    let E₀' := (← chainFn (chain.filter (·.idx ∉ liveRegs)).toList E₀).beta #[E₀]
    let hE' ← mkEqTrans (.fvar hE) partitionProof
    let r ← g.assertAfter hE `hE (← inferType hE') hE'
    let g ← r.mvarId.clear hE
    replaceMainGoal [g]
    let (_, g) ← generalizeOpaque g (hyps := #[r.fvarId]) E₀' `E₀ #[]
    let g ← (← g.clear r.fvarId).clear E₀.fvarId!
    replaceMainGoal [g]

elab "seal" : tactic => runSeal

end

end LeanMLIR.RIR

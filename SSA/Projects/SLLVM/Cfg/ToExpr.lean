/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg.Basic

/-!
# Reflecting a `Cfg` back into a Lean term

`mkCfg` runs at elaboration time on an AST *value*; for its result to become
the body of a `def`, the `Cfg` value must be converted into a Lean `Expr`.
This mirrors `Com.toExprAux` (`Framework/ToExpr.lean`) but is SLLVM-only:
types, contexts and variables go through the identity
`DialectMetaMorphism`, per-instruction `Expr`s through the existing
`Expr.metaMap`, and each CFG constructor is applied with all its implicits
spelled out. Every context is emitted as `Ctxt.ofList ‹literal›`; the kernel
reconciles that with the `↑tys ++ Γ` spellings in the constructor types by
unfolding.
-/

namespace LeanMLIR.SLLVM

open Lean Qq

namespace CfgToExpr

/-- The identity morphism: SLLVM data to expressions of SLLVM data. -/
private def f := DialectMetaMorphism.id SLLVM

private def tyListE (ts : List SLLVM.Ty) : Lean.Expr := f.mapList ts
private def ctxtE (Γ : Ctxt SLLVM.Ty) : Lean.Expr := f.mapCtxt Γ
private def sigsE (sigs : List (List SLLVM.Ty)) : Lean.Expr :=
  _root_.List.foldToExpr (α := q(List SLLVM.Ty)) (sigs.map fun ts => tyListE ts)

private def targetTyE (Γ : Ctxt SLLVM.Ty) (succs : List (List SLLVM.Ty)) : Lean.Expr :=
  mkApp2 (mkConst ``Target) (ctxtE Γ) (sigsE succs)

private def targetE (Γ : Ctxt SLLVM.Ty) :
    {succs : List (List SLLVM.Ty)} → Target Γ succs → Lean.Expr
  | ts :: tss, .here args =>
      mkAppN (mkConst ``Target.here) #[ctxtE Γ, tyListE ts, sigsE tss, f.mapVarVec args]
  | ts :: tss, .there t =>
      mkAppN (mkConst ``Target.there) #[ctxtE Γ, sigsE tss, tyListE ts, targetE Γ t]

private def terminatorE (Γ : Ctxt SLLVM.Ty) (rets : List SLLVM.Ty)
    (succs : List (List SLLVM.Ty)) : Terminator Γ rets succs → Lean.Expr
  | .ret vs =>
      mkAppN (mkConst ``Terminator.ret)
        #[ctxtE Γ, tyListE rets, sigsE succs, f.mapVarVec vs]
  | .br t =>
      mkAppN (mkConst ``Terminator.br)
        #[ctxtE Γ, tyListE rets, sigsE succs, targetE Γ t]
  | .condBr c tT tF =>
      mkAppN (mkConst ``Terminator.condBr)
        #[ctxtE Γ, tyListE rets, sigsE succs, f.mapVar c, targetE Γ tT, targetE Γ tF]
  | .switch (w := w) v dflt cases =>
      let bvTyE := mkApp (mkConst ``BitVec) (toExpr w)
      let casesE := _root_.List.foldToExpr
        (α := mkApp2 (.const ``Prod [0, 0]) bvTyE (targetTyE Γ succs))
        (cases.map fun (val, t) =>
          _root_.Prod.foldToExpr (α := bvTyE) (β := targetTyE Γ succs)
            (toExpr val, targetE Γ t))
      mkAppN (mkConst ``Terminator.switch)
        #[ctxtE Γ, tyListE rets, sigsE succs, toExpr w, f.mapVar v, targetE Γ dflt, casesE]

mutual

private partial def blockComE (rets : List SLLVM.Ty) (succs : List (List SLLVM.Ty)) :
    {Γ Γout : Ctxt SLLVM.Ty} → BlockCom Γ Γout rets succs → MetaM Lean.Expr :=
  fun {Γ} {Γout} b => match b with
  | .term t =>
      return mkAppN (mkConst ``BlockCom.term)
        #[ctxtE Γ, tyListE rets, sigsE succs, terminatorE Γ rets succs t]
  | .var (tys := tys) e body => do
      let eE ← e.metaMap f
      let bodyE ← blockComE rets succs body
      return mkAppN (mkConst ``BlockCom.var)
        #[ctxtE Γ, tyListE tys, ctxtE Γout, tyListE rets, sigsE succs, eE, bodyE]
  | .call (argTys := argTys) (retTys := retTys) (csigs := csigs) (cΓout := cΓout)
      callee centry cblocks args body => do
      let centryE ← blockComE retTys csigs centry
      let cblocksE ← blocksE retTys cΓout cblocks
      let bodyE ← blockComE rets succs body
      return mkAppN (mkConst ``BlockCom.call)
        #[ctxtE Γ, ctxtE Γout, tyListE rets, sigsE succs, tyListE argTys, tyListE retTys,
          sigsE csigs, ctxtE cΓout, toExpr callee, centryE, cblocksE, f.mapVarVec args, bodyE]

private partial def blocksE (rets : List SLLVM.Ty) (Γamb : Ctxt SLLVM.Ty) :
    {sigs : List (List SLLVM.Ty)} → Blocks Γamb rets sigs → MetaM Lean.Expr :=
  fun {sigs} bs => match sigs, bs with
  | [], .nil =>
      return mkAppN (mkConst ``Blocks.nil) #[ctxtE Γamb, tyListE rets]
  | argTys :: sigs, .cons (Γout := Γout) b bs => do
      let bE ← blockComE rets sigs b
      let bsE ← blocksE rets Γamb bs
      return mkAppN (mkConst ``Blocks.cons)
        #[ctxtE Γamb, tyListE rets, tyListE argTys, sigsE sigs, ctxtE Γout, bE, bsE]

end

end CfgToExpr

open CfgToExpr in
/-- Build a (Lean) `Expr` representing a `Cfg` value. -/
def Cfg.toExprM {Γin : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty} (cfg : Cfg Γin rets) :
    MetaM Lean.Expr := do
  match cfg with
  | .mk (sigs := sigs) (Γout := Γout) entry blocks =>
    let entryE ← blockComE rets sigs entry
    let blocksE ← blocksE rets Γout blocks
    return mkAppN (mkConst ``Cfg.mk)
      #[ctxtE Γin, tyListE rets, sigsE sigs, ctxtE Γout, entryE, blocksE]

end LeanMLIR.SLLVM

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.SLLVM.Cfg.OfCom

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

@[expose] public section

namespace LeanMLIR.SLLVM

open Lean Qq

/-- How a `BlockCom.call`'s callee is reflected: by reference to a constant
already in the environment -- the `Com` the callee was lifted to (embedded
through `Cfg.ofCom`), or a `Cfg` constant directly -- or, absent a reference,
inlined as before. A reference keeps the emitted term small and lets the
callee's conformance theorem apply syntactically (`Cfg.denote_mk_ofCom` /
`Cfg.denote_mk_self`); the caller trusts that the constant was lifted from
the same region the binding supplies. -/
inductive CalleeRef
  | com (e : Lean.Expr)
  | cfg (e : Lean.Expr)

namespace CfgToExpr

/-- The identity morphism: SLLVM data to expressions of SLLVM data. -/
def f :=
  DialectMetaMorphism.id SLLVM

def tyListE (ts : List SLLVM.Ty) : Lean.Expr :=
  f.mapList ts

def ctxtE (Γ : Ctxt SLLVM.Ty) : Lean.Expr :=
  f.mapCtxt Γ

def sigsE (sigs : List (List SLLVM.Ty)) : Lean.Expr :=
  _root_.List.foldToExpr (α := q(List SLLVM.Ty)) (sigs.map fun ts => tyListE ts)

def targetTyE (Γ : Ctxt SLLVM.Ty) (succs : List (List SLLVM.Ty)) : Lean.Expr :=
  mkApp2 (mkConst ``Target) (ctxtE Γ) (sigsE succs)

/-- The lookup proof `all[idx]? = some ts` is emitted as `Eq.refl`: both the
list and the index are literals, so the two sides are definitionally equal. -/
def targetE (Γ : Ctxt SLLVM.Ty) {succs : List (List SLLVM.Ty)} (t : Target Γ succs) :
    Lean.Expr :=
  let someTsE := mkApp2 (mkConst ``Option.some [levelZero]) q(List SLLVM.Ty) (tyListE t.ts)
  let hE :=
    mkApp2 (mkConst ``Eq.refl [levelOne]) (mkApp (mkConst ``Option [levelZero]) q(List SLLVM.Ty))
      someTsE
  mkAppN (mkConst ``Target.mk)
    #[ctxtE Γ, sigsE succs, tyListE t.ts, toExpr t.idx, hE, f.mapVarVec t.args]

def terminatorE (Γ : Ctxt SLLVM.Ty) (rets : List SLLVM.Ty) (succs : List (List SLLVM.Ty)) :
    Terminator Γ rets succs → Lean.Expr
  | .ret vs =>
    mkAppN (mkConst ``Terminator.ret) #[ctxtE Γ, tyListE rets, sigsE succs, f.mapVarVec vs]
  | .br t => mkAppN (mkConst ``Terminator.br) #[ctxtE Γ, tyListE rets, sigsE succs, targetE Γ t]
  | .condBr c tT tF =>
    mkAppN (mkConst ``Terminator.condBr)
      #[ctxtE Γ, tyListE rets, sigsE succs, f.mapVar c, targetE Γ tT, targetE Γ tF]
  | .switch (w := w) v dflt cases =>
      let bvTyE := mkApp (mkConst ``BitVec) (toExpr w)
      let casesE :=
      _root_.List.foldToExpr (α := mkApp2 (.const ``Prod [0, 0]) bvTyE (targetTyE Γ succs))
        (cases.map fun (val, t) =>
          _root_.Prod.foldToExpr (α := bvTyE) (β := targetTyE Γ succs) (toExpr val, targetE Γ t))
      mkAppN (mkConst ``Terminator.switch)
      #[ctxtE Γ, tyListE rets, sigsE succs, toExpr w, f.mapVar v, targetE Γ dflt, casesE]

mutual

partial def blockComE (refs : List (String × CalleeRef))
    (rets : List SLLVM.Ty) (succs : List (List SLLVM.Ty)) :
    {Γ Γout : Ctxt SLLVM.Ty} → BlockCom Γ Γout rets succs → MetaM Lean.Expr :=
  fun {Γ} {Γout} b => match b with
  | .term t =>
      return mkAppN (mkConst ``BlockCom.term)
        #[ctxtE Γ, tyListE rets, sigsE succs, terminatorE Γ rets succs t]
  | .var (tys := tys) e body => do
      let eE ← e.metaMap f
      let bodyE ← blockComE refs rets succs body
      return mkAppN (mkConst ``BlockCom.var)
        #[ctxtE Γ, tyListE tys, ctxtE Γout, tyListE rets, sigsE succs, eE, bodyE]
  | .call (argTys := argTys) (retTys := retTys) (csigs := csigs) (cΓout := cΓout)
      callee centry cblocks args body => do
      let bodyE ← blockComE refs rets succs body
      match refs.lookup callee with
      | some ref =>
          -- By reference: the callee's fields are projections of the constant,
          -- so the emitted term never spells out its body.
          let ΓinE := ctxtE (Ctxt.ofList argTys.reverse)
          let cfgE := match ref with
            | .cfg e => e
            | .com e => mkAppN (mkConst ``Cfg.ofCom) #[tyListE retTys, ΓinE, e]
          let proj (fld : Name) : Lean.Expr :=
            mkAppN (mkConst fld) #[ΓinE, tyListE retTys, cfgE]
          return mkAppN (mkConst ``BlockCom.call)
            #[ctxtE Γ, ctxtE Γout, tyListE rets, sigsE succs, tyListE argTys, tyListE retTys,
              proj ``Cfg.sigs, proj ``Cfg.Γout, toExpr callee,
              proj ``Cfg.entry, proj ``Cfg.blocks, f.mapVarVec args, bodyE]
      | none =>
          let centryE ← blockComE refs retTys csigs centry
          let cblocksE ← blocksE refs retTys cΓout csigs cblocks
          return mkAppN (mkConst ``BlockCom.call)
            #[ctxtE Γ, ctxtE Γout, tyListE rets, sigsE succs, tyListE argTys, tyListE retTys,
              sigsE csigs, ctxtE cΓout, toExpr callee, centryE, cblocksE, f.mapVarVec args, bodyE]

partial def blocksE (refs : List (String × CalleeRef))
    (rets : List SLLVM.Ty) (Γamb : Ctxt SLLVM.Ty) (all : List (List SLLVM.Ty)) :
    {remaining : List (List SLLVM.Ty)} → Blocks Γamb rets remaining all → MetaM Lean.Expr :=
  fun {remaining} bs => match remaining, bs with
  | [], .nil =>
      return mkAppN (mkConst ``Blocks.nil) #[ctxtE Γamb, tyListE rets, sigsE all]
  | argTys :: remaining, .cons (Γout := Γout) b bs => do
      let bE ← blockComE refs rets all b
      let bsE ← blocksE refs rets Γamb all bs
      return mkAppN (mkConst ``Blocks.cons)
        #[ctxtE Γamb, tyListE rets, tyListE argTys, sigsE remaining, sigsE all,
          ctxtE Γout, bE, bsE]

end

end CfgToExpr

open CfgToExpr in
/-- Build a (Lean) `Expr` representing a `Cfg` value. -/
def Cfg.toExprM {Γin : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty} (cfg : Cfg Γin rets)
    (refs : List (String × CalleeRef) := []) : MetaM Lean.Expr := do
  match cfg with
  | .mk (sigs := sigs) (Γout := Γout) entry blocks =>
    let entryE ← blockComE refs rets sigs entry
    let blocksE ← blocksE refs rets Γout sigs blocks
    return mkAppN (mkConst ``Cfg.mk)
        #[ctxtE Γin, tyListE rets, sigsE sigs, ctxtE Γout, entryE, blocksE]

end LeanMLIR.SLLVM

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg.Transform
import SSA.Projects.SLLVM.Cfg.ToExpr

/-!
# `[sllvm_cfg| …]` and `[sllvm_cfg_of| …]`

The multi-block siblings of `[sllvm| …]` / `[sllvm_of| …]`: evaluate the
quoted (or bound) AST region, run `mkCfg`, and reflect the resulting `Cfg`
back into a term.

A `with @f := …` binding names a *direct* callee. Bound to a region, the
callee is inlined as before. Bound to an already-lifted `Com` or `Cfg`
constant, it is embedded *by reference*: the constant's value (evaluated
here) supplies the body to the builder, and the emitted term carries only
projections of the constant -- so the callee's conformance theorem applies
syntactically, and its own callees never have to be restated.
-/

namespace LeanMLIR.SLLVM

open Lean Elab Term Qq
open MLIR.AST

private instance : Inhabited ParsedCfg :=
  ⟨⟨(∅ : Ctxt SLLVM.Ty), [], ⟨.term (.ret .nil), .nil⟩⟩⟩

/-- The callee's `Cfg` value, packaged for `evalParsedCfg`. -/
private def ParsedCfg.ofCfg {Γin : Ctxt SLLVM.Ty} {rets : List SLLVM.Ty} (c : Cfg Γin rets) :
    ParsedCfg :=
  ⟨Γin, rets, c⟩

@[inherit_doc ParsedCfg.ofCfg]
private def ParsedCfg.ofComRef {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty}
    (c : Com SLLVM Γ .impure ts) : ParsedCfg :=
  ⟨Γ, ts, Cfg.ofCom c⟩

private unsafe def evalParsedCfgAux : Q(ParsedCfg) → MetaM ParsedCfg :=
  Lean.Meta.evalExpr ParsedCfg q(ParsedCfg)

/-
SAFETY: as `evalExprOfTypeRegion` -- the `implemented_by` is safe assuming
`ParsedCfg` and `q(ParsedCfg)` agree.
-/
@[implemented_by evalParsedCfgAux]
private partial def evalParsedCfg : Q(ParsedCfg) → MetaM ParsedCfg :=
  default

private def elabCfgOfRegion (ast : MLIR.AST.Region 0) : TermElabM Lean.Expr := do
  match mkCfg (foldGepZeroIndex ast) with
  | .error (e : TransformError) => throwError (repr e)
  | .ok ⟨_, _, cfg⟩ => cfg.toExprM

/-- Evaluate a term to the AST region it denotes. -/
private def elabRegionTerm (t : Term) : TermElabM (MLIR.AST.Region 0) := do
  let e ← elabTermEnsuringTypeQ t q(MLIR.AST.Region 0)
  synthesizeSyntheticMVarsNoPostponing
  SSA.evalExprOfTypeRegion 0 (← instantiateMVars e)

/-- A `with` binding, classified by its term's type: a `Region` is spliced
and inlined; a lifted `Com` or `Cfg` is embedded by reference. -/
private inductive CalleeBinding
  | region (r : MLIR.AST.Region 0)
  | ref (r : CalleeRef) (v : ParsedCfg)

private def elabCalleeBinding (t : Term) : TermElabM CalleeBinding := do
  let e ← Term.elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← Lean.Meta.whnfR (← Lean.Meta.inferType e)
  if ty.isAppOf ``MLIR.AST.Region then
    return .region (← SSA.evalExprOfTypeRegion 0 e)
  else if ty.isAppOf ``Com then
    let args := ty.getAppArgs
    -- `Com d [inst] Γ eff ty`
    unless args.size == 5 do
      throwError "malformed `Com` type: {ty}"
    let v ← evalParsedCfg <| mkAppN (mkConst ``ParsedCfg.ofComRef) #[args[2]!, args[4]!, e]
    return .ref (.com e) v
  else if ty.isAppOf ``Cfg then
    let args := ty.getAppArgs
    unless args.size == 2 do
      throwError "malformed `Cfg` type: {ty}"
    let v ← evalParsedCfg <| mkAppN (mkConst ``ParsedCfg.ofCfg) #[args[0]!, args[1]!, e]
    return .ref (.cfg e) v
  else
    throwError "a callee binding must be an `MLIR.AST.Region 0` (inlined) or a \
      lifted `Com`/`Cfg` (embedded by reference); it has type{Lean.indentExpr ty}"

private def elabCfgCalleeTable (bs : Array (TSyntax ``sllvmCallee)) :
    TermElabM (List (String × CalleeBinding)) :=
  bs.toList.mapM fun b => do
    match b with
    | `(sllvmCallee| @$name:ident := $t) =>
      return (name.getId.toString, ← elabCalleeBinding t)
    | _ =>
      throwUnsupportedSyntax

private def elabCfgWithBindings (ast : MLIR.AST.Region 0)
    (table : List (String × CalleeBinding)) : TermElabM Lean.Expr := do
  let regions := table.filterMap fun (n, b) =>
    match b with | .region r => some (n, r) | _ => none
  let refs := table.filterMap fun (n, b) =>
    match b with | .ref r _ => some (n, r) | _ => none
  let vals := table.filterMap fun (n, b) =>
    match b with | .ref _ v => some (n, v) | _ => none
  match mkCfg (foldGepZeroIndex (bindCallees regions ast)) vals with
  | .error (e : TransformError) => throwError (repr e)
  | .ok ⟨_, _, cfg⟩ => cfg.toExprM refs

elab "[sllvm_cfg| " reg:mlir_region "]" : term => do
  elabCfgOfRegion (← elabRegionTerm (← `([mlir_region|$reg])))

/-- `[sllvm_cfg| ‹region› with @f := …]` binds the bodies of the symbols the
region's `llvm.call`s name; each call becomes a `BlockCom.call`. A region
binding is inlined; a `Com`/`Cfg` binding is embedded by reference. -/
elab "[sllvm_cfg| " reg:mlir_region " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCfgCalleeTable bs.getElems
  elabCfgWithBindings (← elabRegionTerm (← `([mlir_region|$reg]))) table

/-- `[sllvm_cfg| …]` from an already-built `MLIR.AST.Region 0`, so a lifted
region can stay the single source of truth. -/
elab "[sllvm_cfg_of| " t:term "]" : term => do
  elabCfgOfRegion (← elabRegionTerm t)

/-- `[sllvm_cfg_of| r with @f := …]`: `[sllvm_cfg_of| r]` with callee
bindings. -/
elab "[sllvm_cfg_of| " t:term " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCfgCalleeTable bs.getElems
  elabCfgWithBindings (← elabRegionTerm t) table


open Lean Elab Command Meta in
/-- `sllvm_cfg_def X : Cfg Γin rets := v` defines a lifted program so that no tactic has to unfold
all of it. The pieces become constants:
* `X.cfgCtx`, `X.cfgSigs` (reducible): the literal out-context and block signatures;
* `X.cfgEntry`, `X.cfgBlock_i` (reducible): one definition per block body;
* `X.cfgBlocks`: the chain of `X.cfgBlock_i`, the one piece that stays folded;
* `X` (`implicit_reducible`): `⟨X.cfgEntry, X.cfgBlocks⟩`.
Unfolding `X` then shows names only, so `X.Γout` is the literal context at `implicit`
transparency, and entering a block unfolds that block alone. -/
elab mods:declModifiers "sllvm_cfg_def " id:ident " : " ty:term " := " val:term : command => do
  let name := (← getCurrNamespace) ++ id.getId
  let _ := mods
  liftTermElabM do
    let tyE ← elabType ty
    let v ← elabTermEnsuringType val tyE
    synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    let tyE ← instantiateMVars tyE
    let_expr Cfg.mk Γin rets sigs Γout entry blocks := v
      | throwError "sllvm_cfg_def: expected a `Cfg.mk` value, got{indentExpr v}"
    let add (n : Name) (t e : Expr) (st : ReducibilityStatus) : TermElabM Expr := do
      let env ← getEnv
      let hints := if st == .reducible then ReducibilityHints.abbrev
        else .regular (getMaxHeight env e + 1)
      addAndCompile <| .defnDecl (← mkDefinitionValInferringUnsafe n [] t e hints)
      setReducibilityStatus n st
      addDeclarationRangesFromSyntax n (← getRef)
      return mkConst n
    let ctx ← add (name ++ `cfgCtx) (← inferType Γout) Γout .reducible
    let sigsC ← add (name ++ `cfgSigs) (← inferType sigs) sigs .reducible
    -- a type as `BlockCom`/`Blocks` over the named context and signatures
    let named (t : Expr) : Expr := t.replace fun e =>
      if e == Γout then some ctx else if e == sigs then some sigsC else none
    let entryC ← add (name ++ `cfgEntry) (named (← inferType entry)) entry .reducible
    let rec chain (fuel : Nat) (e : Expr) (i : Nat) : TermElabM Expr := do
      let fuel + 1 := fuel | throwError "sllvm_cfg_def: too many blocks"
      match_expr e with
      | Blocks.cons _Γamb rets' argTys rem _all Γo b bs =>
        let bC ← add (name ++ Name.mkSimple s!"cfgBlock_{i}") (named (← inferType b)) b .reducible
        return mkApp8 (mkConst ``Blocks.cons) ctx rets' argTys rem sigsC Γo bC (← chain fuel bs (i + 1))
      | Blocks.nil _Γamb rets' _all => return mkApp3 (mkConst ``Blocks.nil) ctx rets' sigsC
      | _ => throwError "sllvm_cfg_def: unexpected blocks{indentExpr e}"
    let blocksV ← chain 10000 blocks 0
    let blocksC ← add (name ++ `cfgBlocks) (mkApp4 (mkConst ``Blocks) ctx rets sigsC sigsC) blocksV
      .semireducible
    let _ ← add name tyE (mkApp6 (mkConst ``Cfg.mk) Γin rets sigsC ctx entryC blocksC)
      .implicitReducible

end LeanMLIR.SLLVM

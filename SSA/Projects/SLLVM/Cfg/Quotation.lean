/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg.Transform
import SSA.Projects.SLLVM.Cfg.ToExpr

/-!
# `[sllvm_cfg| …]` and `[sllvm_cfg_of| …]`

The multi-block siblings of `[sllvm| …]` / `[sllvm_of| …]`: evaluate the
quoted (or bound) AST region, run `mkCfg`, and reflect the resulting `Cfg`
back into a term. No callee bindings -- calls inside CFG blocks are not
supported.
-/

namespace LeanMLIR.SLLVM

open Lean Elab Term Qq
open MLIR.AST

private def elabCfgOfRegion (ast : MLIR.AST.Region 0) : TermElabM Lean.Expr := do
  match mkCfg ast with
  | .error (e : TransformError) => throwError (repr e)
  | .ok ⟨_, _, cfg⟩ => cfg.toExprM

/-- Evaluate a term to the AST region it denotes. -/
private def elabRegionTerm (t : Term) : TermElabM (MLIR.AST.Region 0) := do
  let e ← elabTermEnsuringTypeQ t q(MLIR.AST.Region 0)
  synthesizeSyntheticMVarsNoPostponing
  SSA.evalExprOfTypeRegion 0 (← instantiateMVars e)

private def elabCfgCalleeTable (bs : Array (TSyntax ``sllvmCallee)) :
    TermElabM (List (String × MLIR.AST.Region 0)) :=
  bs.toList.mapM fun b => do
    match b with
    | `(sllvmCallee| @$name:ident := $t) =>
        return (name.getId.toString, ← elabRegionTerm t)
    | _ => throwUnsupportedSyntax

elab "[sllvm_cfg| " reg:mlir_region "]" : term => do
  elabCfgOfRegion (← elabRegionTerm (← `([mlir_region| $reg])))

/-- `[sllvm_cfg| ‹region› with @f := fRegion]` binds the bodies of the
symbols the region's `llvm.call`s name, exactly as `[sllvm| … with …]` does;
each call becomes a `BlockCom.call` whose callee is itself a `Cfg`. -/
elab "[sllvm_cfg| " reg:mlir_region " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCfgCalleeTable bs.getElems
  elabCfgOfRegion (bindCallees table (← elabRegionTerm (← `([mlir_region| $reg]))))

/-- `[sllvm_cfg| …]` from an already-built `MLIR.AST.Region 0`, so a lifted
region can stay the single source of truth. -/
elab "[sllvm_cfg_of| " t:term "]" : term => do
  elabCfgOfRegion (← elabRegionTerm t)

/-- `[sllvm_cfg_of| r with @f := fRegion]`: `[sllvm_cfg_of| r]` with callee
bindings. -/
elab "[sllvm_cfg_of| " t:term " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCfgCalleeTable bs.getElems
  elabCfgOfRegion (bindCallees table (← elabRegionTerm t))

end LeanMLIR.SLLVM

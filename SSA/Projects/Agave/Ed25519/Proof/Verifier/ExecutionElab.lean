module

public import SSA.Projects.RIR.Syntax.Elab
public meta import SSA.Projects.RIR.Syntax.Elab

/-!
An exact-region importer using the ordinary RIR parser and instruction emitter,
with explicitly typed `EffectM` primitives at external calls. Unlike `mlir_def`,
this inserts the supplied effect directly; it does not wrap it in another call
frame. All emitted terms are checked by the kernel. This module only changes
callee binding, not instruction parsing, flags, globals, or block translation.
-/

namespace LeanMLIR.RIR.ExecutionImport

open Lean Elab Command Term MLIR

public meta section

private def checkPrimitiveCallee
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (t : TSyntax `term) (ts us : List Ty) : CommandElabM Unit := do
  let expected ← `(Vals $(← MlirDef.tysStx ts) → EffectM (Vals $(← MlirDef.tysStx us)))
  runTermElabM fun _ =>
    Term.elabBinders binders fun _ => do
      let ty ← Term.elabType expected
      discard <| Term.elabTermEnsuringType t ty
      Term.synthesizeSyntheticMVarsNoPostponing

open MlirDef in
/-- Define `x` from the region, as described in the module docstring. -/
def elabExecutionDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (x : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (r : TSyntax `mlir_region) (callees globalMap : Array (TSyntax ``calleeBinding)) :
    CommandElabM Unit := do
  let rgn ← liftCoreM (region r)
  let p ← match Prog.ofRegion rgn with
    | .ok p => pure p
    | .error e => throwErrorAt r e
  let table ← callees.toList.mapM fun (c : TSyntax ``calleeBinding) => match c with
    | `(calleeBinding| @$f:ident := $t) => pure (f.getId.toString, t)
    | `(calleeBinding| @$f:str := $t) => pure (f.getString, t)
    | c => throwErrorAt c "malformed callee binding"
  let globalTable ← globalMap.toList.mapM fun (c : TSyntax ``calleeBinding) => match c with
    | `(calleeBinding| @$f:ident := $t) => pure (f.getId.toString, t)
    | `(calleeBinding| @$f:str := $t) => pure (f.getString, t)
    | c => throwErrorAt c "malformed global address binding"
  unless (globalTable.map Prod.fst).eraseDups.length == globalTable.length do
    throwErrorAt r "duplicate global address binding"
  for b in p.blocks do
    for instr in b.body do
      if let .globalAddr symbol _ := instr then
        unless (globalTable.lookup symbol).isSome do
          throwErrorAt r "llvm.mlir.addressof @{symbol}: no address bound; add `globals @{symbol} := …`"
  let global (f : String) : TSyntax `term :=
    (globalTable.lookup f).getD (mkIdent (.mkSimple f))
  -- every callee's term, checked against its call sites
  let calls := p.blocks.flatMap fun b => b.body.filterMap fun
    | .call f ts us _ _ => some (f, ts, us)
    | _ => none
  let mut terms : List (String × TSyntax `term) := []
  for (f, ts, us) in calls do
    if (terms.lookup f).isNone then
      let t ← calleeTerm r table f
      checkPrimitiveCallee binders t ts us
      terms := terms ++ [(f, t)]
  for (f, _) in table do
    unless (terms.lookup f).isSome do
      logWarning m!"@{f} is bound but never called"
  let callee (f : String) : TSyntax `term := (terms.lookup f).getD (mkIdent (.mkSimple f))
  -- the binders each block needs: those its callees' terms mention
  let binderNames ← binders.mapM fun b => getBracketedBinderIds b
  let blockBinders (b : PBlock) :
      Array (TSyntax ``Lean.Parser.Term.bracketedBinder) × Array Ident :=
    let used := b.body.flatMap fun
      | .call f .. => (idents (callee f)).toList
      | .globalAddr f _ => (idents (global f)).toList
      | _ => []
    let keep := (binders.zip binderNames).filter fun (_, ns) => ns.any (binderUsed used)
    (keep.map (·.1), keep.flatMap fun (_, ns) => ns.map mkIdent)
  let n := p.blocks.length
  let name (s : Name) : Ident := mkIdent (x.getId ++ s)
  let Γ := name `Γ
  let blockTys := name `blockTys
  let blockParams := name `blockParams
  let tree := name `tree
  let tys : ValTys := { hty := name `hty, vals := p.Γ.vals }
  let blockName (b : PBlock) : Ident := name (if n == 1 then `entry else .mkSimple b.name)
  let tRets ← tysStx p.tRets
  let cmds ← do
    let paramTys (b : PBlock) := b.params.map fun i => (p.Γ.vals[i]?).getD (.bv 0)
    let fins := List.range n
    let valueCount := num p.Γ.n
    let blockCount := num n
    let Γdef ←
      -- the kernel checks the count: the elaborator would recurse once per value
      `(abbrev $Γ : Ctx :=
          ⟨$valueCount, $(← tysStx p.Γ.args), $(← tysStx p.Γ.vals), by decide +kernel⟩)
    let d := depth p.Γ.n
    let treeDepth := num d
    let treeDef ← `(abbrev $tree : TyTree := $(← treeStx (TyTree.ofList d p.Γ.vals)))
    -- the kernel checks the trie against `Γ.vals` once
    let htyDef ←
      `(theorem $(tys.hty) (k : Fin ($Γ).n) (t : Ty) (h : ($tree).get k = t) : ($Γ).ty k = t :=
          (Ctx.ty_eq_get (d := $treeDepth) (by decide +kernel) (by decide) k).trans h)
    let tysDef ←
      if n == 1 then `(abbrev $blockTys : Fin 1 → List Ty := fun _ => [])
      else
        let alts ← (fins.zip p.blocks).filterMapM fun (k, b) => do
          if b.params.isEmpty then return none
          let tys ← tysStx (paramTys b)
          let index := num k
          return some (← `(Lean.Parser.Term.matchAltExpr| | ⟨$index, _⟩ => $tys))
        let alts := alts.toArray.push (← `(Lean.Parser.Term.matchAltExpr| | _ => []))
        `(abbrev $blockTys : Fin $blockCount → List Ty := fun $alts:matchAlt*)
    let paramsDef ←
      if n == 1 then
        `(abbrev $blockParams : (k : Fin 1) → Dsts $Γ ($blockTys k) := fun _ => .nil)
      else
        let values ← p.blocks.toArray.mapM fun b => do
          consStx (← b.params.mapM (dstStx tys))
        let body ← finCases values
        `(abbrev $blockParams : (k : Fin $blockCount) → Dsts $Γ ($blockTys k) :=
            $body)
    let blockDefs ← p.blocks.toArray.mapM fun b => do
      let (bs, _) := blockBinders b
      let body ← b.body.toArray.mapM (instrStx tys callee global)
      `(def $(blockName b) $bs* : BasicBlock $Γ $tRets $blockTys :=
          { body := [$body,*], exit := $(← exitStx tys b.exit) })
    let blocksVal ←
      if let [b] := p.blocks then `(fun _ => $(blockName b) $((blockBinders b).2)*)
      else
        let values ← p.blocks.toArray.mapM fun b => do
          let (_, args) := blockBinders b
          `($(blockName b) $args*)
        finCases values
    let funcDef ←
      `($[$doc?:docComment]? @[reducible] def $x $binders* : Func :=
          { Γ := $Γ, tRets := $tRets, n := $blockCount, blockTys := $blockTys,
            blockParams := $blockParams, hhasBlock := by decide, hentry := rfl,
            blocks := $blocksVal })
    let argNames := (List.range p.Γ.args.length).map fun i => mkIdent (.mkSimple s!"arg{i}")
    let argBinders ← (argNames.zip p.Γ.args).toArray.mapM fun (a, t) => do
      `(Lean.Parser.Term.bracketedBinderF| ($a : ⟦($(← tyStx t) : Ty)⟧))
    let argsDef ←
      `(def $(name `args) $argBinders* : Vals ($Γ).args := $(← consStx (argNames.map (⟨·.raw⟩))))
    pure (#[Γdef, treeDef, htyDef, tysDef, paramsDef] ++ blockDefs ++ #[funcDef, argsDef])
  for c in cmds do
    elabCommand c


end

/-- Import the exact region with raw, exactly typed external effects. -/
syntax (name := executionDef) (docComment)? "execution_def " ident (ppSpace bracketedBinder)* " := "
  mlir_region (" with " calleeBinding,+)? (" globals " calleeBinding,+)? : command

elab_rules : command
  | `($[$doc?:docComment]? execution_def $x:ident $bs* := $r:mlir_region $[with $cs,*]? $[globals $gs,*]?) =>
    elabExecutionDef doc? x bs r ((cs.map (·.getElems)).getD #[])
      ((gs.map (·.getElems)).getD #[])

end LeanMLIR.RIR.ExecutionImport

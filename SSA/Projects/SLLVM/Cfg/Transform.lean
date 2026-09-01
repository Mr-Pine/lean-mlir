/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Cfg.Basic
import SSA.Projects.SLLVM.Dialect.Syntax.Parser

/-!
# AST → `Cfg`

`mkCfg` is `mkCom`'s multi-block sibling: it turns a parsed `MLIR.AST.Region`
-- back-edges included -- into a `Cfg`. Per-operation building is
the existing `TransformExpr SLLVM` instance, so everything the straight-line
parser accepts (gep included) works inside a block.

Scoping is depth-1 dominance: the name mapping is snapshotted after the entry
block, and every tail block restores that snapshot before declaring its own
arguments -- so a block resolves entry definitions, region arguments, and its
own arguments, and nothing else. The mapping and the context stay in sync
because both grow cons-first: a block's context is
`Ctxt.ofList argTys.reverse ++ Γamb` *by construction*, no casts.

Terminators are decoded from each block's last operation. Successor operands
live in the op's main operand list, split by `operandSegmentSizes` (and, for
`llvm.switch`, `case_operand_segments` / `case_values`).
-/

namespace LeanMLIR.SLLVM

open MLIR.AST

/-- Index of successor `name` in the region's block list. Any block may be
named -- back-edges included; see `Cfg/Basic.lean` for the semantics. -/
def resolveSucc (all : List String) (name : String) : ExceptM SLLVM Nat :=
  match all.idxOf? name with
  | some r => return r
  | none => throw <| .generic s!"^{name}: unknown block"

/-- The operands `vals`, resolved in `Γ` at the expected types `tys` -- the
argument vector a branch passes to its target block. -/
def mkArgsHVector (Γ : Ctxt SLLVM.Ty) :
    (vals : List (TypedSSAVal 0)) → (tys : List SLLVM.Ty) →
    ReaderM SLLVM (HVector Γ.Var tys)
  | [], [] => return .nil
  | v :: vs, t :: ts => do
      let var ← getValFromCtxt Γ (SSAValToString v.1) t
      return .cons var (← mkArgsHVector Γ vs ts)
  | vals, tys => throw <| .generic s!"expected {tys.length} block argument(s), \
      found {vals.length}"

/-- The target at block index `r`, carrying `argVals`. -/
def mkTarget (Γ : Ctxt SLLVM.Ty) (argVals : List (TypedSSAVal 0))
    (succs : List (List SLLVM.Ty)) (r : Nat) : ReaderM SLLVM (Target Γ succs) := do
  match h : succs[r]? with
  | some ts => return ⟨r, h, ← mkArgsHVector Γ argVals ts⟩
  | none => throw <| .generic "internal: successor index out of range"

private def segAttr (opStx : Op 0) (attr : String) : ReaderM SLLVM (List Nat) := do
  return (← arrayInts opStx attr).map (·.toNat)

/-- Decode a block's final operation into a `Terminator`. `all` names every
non-entry block, in order -- what its branches may target. -/
def mkTerminator (rets : List SLLVM.Ty) (succs : List (List SLLVM.Ty))
    (all : List String) (Γ : Ctxt SLLVM.Ty) (opStx : Op 0) :
    ReaderM SLLVM (Terminator Γ rets succs) := do
  match opStx.name with
  | "llvm.return" =>
      return .ret (← mkArgsHVector Γ opStx.args rets)
  | "llvm.br" => do
      let [s] := opStx.successors
        | throw <| .generic "llvm.br: expected exactly one successor"
      let r ← resolveSucc all s
      return .br (← mkTarget Γ opStx.args succs r)
  | "llvm.cond_br" => do
      let [sT, sF] := opStx.successors
        | throw <| .generic "llvm.cond_br: expected exactly two successors"
      let [nC, nT, nF] ← segAttr opStx "operandSegmentSizes"
        | throw <| .generic "llvm.cond_br: malformed `operandSegmentSizes`"
      let c :: rest := opStx.args
        | throw <| .generic "llvm.cond_br: expected a condition operand"
      unless nC == 1 && rest.length == nT + nF do
        throw <| .generic "llvm.cond_br: operands do not match `operandSegmentSizes`"
      let cVar ← getValFromCtxt Γ (SSAValToString c.1) (Ty.bitvec 1)
      let tT ← mkTarget Γ (rest.take nT) succs (← resolveSucc all sT)
      let tF ← mkTarget Γ (rest.drop nT) succs (← resolveSucc all sF)
      return .condBr cVar tT tF
  | "llvm.switch" => do
      let dfltName :: caseNames := opStx.successors
        | throw <| .generic "llvm.switch: expected at least a default successor"
      let scrut :: restArgs := opStx.args
        | throw <| .generic "llvm.switch: expected a scrutinee operand"
      let ⟨t, _⟩ ← TypedSSAVal.mkVal (φ := 0) Γ scrut
      let Ty.bitvec w := t
        | throw <| .generic s!"llvm.switch: scrutinee must be an integer, found {t}"
      let vVar ← getValFromCtxt Γ (SSAValToString scrut.1) (Ty.bitvec w)
      let [_, nDef, _] ← segAttr opStx "operandSegmentSizes"
        | throw <| .generic "llvm.switch: malformed `operandSegmentSizes`"
      let caseSegs ← if caseNames.isEmpty then pure [] else segAttr opStx "case_operand_segments"
      let caseVals ← match opStx.getAttr? "case_values" with
        | none => pure []
        | some (.dense v _) => (denseInts v : ExceptM SLLVM _)
        | some _ => throw <| .generic "llvm.switch: `case_values` must be a `dense<…>` attribute"
      unless caseVals.length == caseNames.length && caseSegs.length == caseNames.length do
        throw <| .generic "llvm.switch: `case_values`/`case_operand_segments` do not match \
          the successor list"
      let dflt ← mkTarget Γ (restArgs.take nDef) succs (← resolveSucc all dfltName)
      let mut caseArgs := restArgs.drop nDef
      let mut cases : List (BitVec w × Target Γ succs) := []
      for (val, name, n) in caseVals.zip (caseNames.zip caseSegs) do
        let tgt ← mkTarget Γ (caseArgs.take n) succs (← resolveSucc all name)
        cases := cases ++ [(BitVec.ofInt w val, tgt)]
        caseArgs := caseArgs.drop n
      return .switch vVar dflt cases
  | name => throw <| .generic s!"'{name}' is not a terminator -- every block must end in \
      llvm.return, llvm.br, llvm.cond_br or llvm.switch"

/-- A built callee: its argument context, return types, and body. -/
abbrev ParsedCfg : Type :=
  Σ (Γin : Ctxt SLLVM.Ty) (rets : List SLLVM.Ty), Cfg Γin rets

/-- `MkCallee` builds a callee's (already spliced-in) region into a `Cfg`.
Passed to `mkBlockCom` as data so its recursion stays structural; the fuel
lives in `mkCfgAux`. -/
abbrev MkCallee : Type := MLIR.AST.Region 0 → BuilderM SLLVM ParsedCfg

/-- The three AVX-512 IFMA intrinsics keep their keyhole treatment as
ordinary (region-free) operations; see the straight-line parser. -/
private def isIntrinsicCall (opStx : Op 0) : Bool :=
  match opStx.getAttr? "callee" with
  | some (.symbol c) =>
      c == "x86_avx512_vpmadd52l_uq_512" || c == "x86_avx512_vpmadd52h_uq_512"
        || c == "x86_avx512_vpermi2var_q_512"
  | _ => false

/-- Fold a block's body: every non-terminator op through the straight-line
`TransformExpr` machinery (coerced impure), the last op through
`mkTerminator`. Mirrors `mkComHelper`. An `llvm.call` becomes a
`BlockCom.call` node whose callee -- bound beforehand, like the `Com` path's
`with @f := …` -- is built by `mkCallee` as a `Cfg` of its own (a
straight-line callee is the one-block case). -/
def mkBlockCom (mkCallee : MkCallee) (valTable : List (String × ParsedCfg))
    (rets : List SLLVM.Ty)
    (succs : List (List SLLVM.Ty)) (all : List String) :
    (Γ : Ctxt SLLVM.Ty) → List (Op 0) → BuilderM SLLVM (Σ Γout, BlockCom Γ Γout rets succs)
  | Γ, [termStx] => do
      return ⟨Γ, .term (← mkTerminator rets succs all Γ termStx)⟩
  | Γ, opStx :: rest => do
      if opStx.name == "llvm.call" && !isIntrinsicCall opStx then
        let some (.symbol callee) := opStx.getAttr? "callee"
          | throw <| .generic "llvm.call: expected a `callee` symbol attribute"
        let args ← opStx.parseArgs Γ
        let argTys := args.types
        let retTys ← opStx.res.mapM (fun r => mkTy r.2)
        -- A spliced region wins; otherwise the callee's already-lifted constant
        -- (evaluated into `valTable` by the quotation) supplies the body.
        let ⟨cΓin, crets, ccfg⟩ ← match opStx.regions[0]? with
          | some calleeReg => mkCallee calleeReg
          | none => match valTable.lookup callee with
            | some p => pure p
            | none => throw <| .unsupportedOp s!"llvm.call to {callee}: the callee's \
                body is not bound. Supply it with `with @{callee} := …` or define a \
                lifted `{callee}` in scope."
        if hΓ : cΓin = Ctxt.ofList argTys.reverse then
          if hr : crets = retTys then
            let ccfg : Cfg (Ctxt.ofList argTys.reverse) retTys := hΓ ▸ hr ▸ ccfg
            let .mk centry cblocks := ccfg
            let _ ← (opStx.res.zip retTys).foldlM (init := Γ) fun Γ (var, ty) => do
              let ⟨Γ', _⟩ ← addValToMapping Γ (SSAValToString var.1) ty
              return Γ'
            let ⟨Γout, body⟩ ← mkBlockCom mkCallee valTable rets succs all (retTys ++ Γ) rest
            return ⟨Γout, .call callee centry cblocks args.toHVector body⟩
          else
            throw <| .generic s!"llvm.call to {callee}: the callee returns \
              {repr crets}, but the call site expects {repr retTys}"
        else
          throw <| .generic s!"llvm.call to {callee}: the callee takes \
              {repr cΓin}, but the call site passes {repr argTys}"
      else
      unless opStx.regions.isEmpty do
        throw <| .generic s!"'{opStx.name}': operations with regions are not \
          supported inside a CFG block"
      let ⟨_eff, tys, e⟩ ← (TransformExpr.mkExpr Γ opStx [] :
        ReaderM SLLVM (Σ eff ty, Expr SLLVM Γ eff ty))
      if opStx.res.length != tys.length then
        throw <| .generic s!"'{opStx.name}': expected {tys.length} result name(s), \
          found {opStx.res.length}"
      let _ ← (opStx.res.zip tys).foldlM (init := Γ) fun Γ (var, ty) => do
        let ⟨Γ', _⟩ ← addValToMapping Γ (SSAValToString var.1) ty
        return Γ'
      let ⟨Γout, body⟩ ← mkBlockCom mkCallee valTable rets succs all (tys ++ Γ) rest
      return ⟨Γout, .var (e.changeEffect (EffectKind.le_impure _)) body⟩
  | _, [] => throw <| .generic "empty block: every block must end in a terminator"

/-- Record a block's argument names (types are fixed by the caller). -/
private def declareBlockArgNames (args : List (TypedSSAVal 0)) : BuilderM SLLVM Unit := do
  for (name, _) in args do
    let some nm := (← get).add (SSAValToString name)
      | throw <| .nameAlreadyDeclared (SSAValToString name)
    set nm

/-- Build the tail blocks. `snapshot` is the name mapping right after the
entry block -- restoring it before each block is what enforces depth-1
dominance. `sigsAll` is every block's signature: each block's branches may
target the whole list. -/
def mkBlocks (mkCallee : MkCallee) (valTable : List (String × ParsedCfg))
    (all : List String) (rets : List SLLVM.Ty)
    (Γamb : Ctxt SLLVM.Ty) (snapshot : NameMapping)
    (sigsAll : List (List SLLVM.Ty)) :
    (bs : List (MLIR.AST.Block 0)) → (sigs : List (List SLLVM.Ty)) →
    BuilderM SLLVM (Blocks Γamb rets sigs sigsAll)
  | [], [] => return .nil
  | b :: bs, argTys :: sigs => do
      unless b.args.length == argTys.length do
        throw <| .generic "internal: block arguments out of sync with signature"
      set snapshot
      declareBlockArgNames b.args
      let ⟨_Γout, body⟩ ←
        try
          mkBlockCom mkCallee valTable rets sigsAll all
            (Ctxt.ofList argTys.reverse ++ Γamb) b.ops
        catch
          | .undeclaredName n => throw <| .generic s!"%{n} is not in scope in ^{b.name}: \
              a CFG block may only use entry-block definitions and its own arguments \
              (depth-1 dominance)"
          | e => throw e
      let rest ← mkBlocks mkCallee valTable all rets Γamb snapshot sigsAll bs sigs
      return .cons body rest
  | _, _ => throw <| .generic "internal: blocks out of sync with signatures"

/-- The region's return types: read off its first `llvm.return`. Every other
return is checked against them when its terminator is built. -/
private def findRets (reg : Region 0) : ExceptM SLLVM (List SLLVM.Ty) := do
  let allOps := reg.ops ++ reg.blocks.flatMap (·.ops)
  let some retStx := allOps.find? (·.name == "llvm.return")
    | throw <| .generic "region has no llvm.return"
  retStx.args.mapM (TypedSSAVal.mkTy ·)

/-- The `mkCfg` body, with callee-building supplied as data. -/
def mkCfgCore (mkCallee : MkCallee) (valTable : List (String × ParsedCfg))
    (reg : Region 0) : BuilderM SLLVM ParsedCfg := do
  let sigTable ← reg.blocks.mapM fun b => do
    let tys ← (b.args.mapM (TypedSSAVal.mkTy ·) : ExceptM SLLVM _)
    return (b.name, tys)
  let names := sigTable.map (·.1)
  unless names.eraseDups.length == names.length do
    throw <| .generic "duplicate block name"
  let rets ← findRets reg
  let entryArgTys ← (reg.args.mapM (TypedSSAVal.mkTy ·) : ExceptM SLLVM _)
  declareBlockArgNames reg.args
  let Γin := Ctxt.ofList entryArgTys.reverse
  let ⟨Γout, entry⟩ ← mkBlockCom mkCallee valTable rets (sigTable.map (·.2)) names Γin reg.ops
  let snapshot ← get
  let blocks ← mkBlocks mkCallee valTable names rets Γout snapshot
    (sigTable.map (·.2)) reg.blocks (sigTable.map (·.2))
  return ⟨Γin, rets, ⟨entry, blocks⟩⟩

/-- Callee building with a nesting bound: each level of call nesting spends
one unit of fuel (the bound is not a real restriction, exactly as in
`mkComAux`). A callee is its own scope, so it gets a fresh name mapping. -/
def mkCfgAux (valTable : List (String × ParsedCfg)) : Nat → MkCallee
  | 0, _ => throw <| .generic "call nesting is too deep"
  | fuel + 1, reg => do
      let saved ← get
      set ([] : NameMapping)
      let r ← mkCfgCore (mkCfgAux valTable fuel) valTable reg
      set saved
      return r

/-- The maximum call nesting `mkCfg` will accept. -/
def maxCallDepth : Nat := 64

/-- Turn a (possibly multi-block, forward-branching) region into a `Cfg`.
Calls become `BlockCom.call` nodes; their callees must have been bound into
the ops beforehand (`bindCallees`, surfaced as `with @f := …`). -/
def mkCfg (reg : Region 0) (valTable : List (String × ParsedCfg) := []) :
    ExceptM SLLVM (Σ (Γin : Ctxt SLLVM.Ty) (rets : List SLLVM.Ty), Cfg Γin rets) :=
  BuilderM.runWithEmptyMapping <| mkCfgCore (mkCfgAux valTable maxCallDepth) valTable reg

end LeanMLIR.SLLVM

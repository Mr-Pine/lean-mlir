module

public import SSA.Projects.RIR.Syntax.Parser
public import SSA.Projects.RIR.Syntax.Translate
public import SSA.Projects.RIR.Semantics.Func
public import SSA.Projects.RIR.TyTree
public meta import SSA.Projects.RIR.Syntax.Parser
public meta import SSA.Projects.RIR.Syntax.Translate
public meta import SSA.Projects.RIR.TyTree
public meta import Lean.Elab.Command

/-!
# `mlir_def`

`mlir_def X binders := { region } with @f := t, …` translates a generic-form MLIR region and
defines it in the shape of a hand lift:
* `X.Γ`, `X.tree`, `X.blockTys`, `X.blockParams` (`abbrev`s), and `X.hty`, which proves a value
  register's type from `X.tree`;
* one `def` per block: `X.entry` for a single block, else `X.bb0`, `X.bb1`, … by MLIR name;
* `X : Func` (`@[reducible]`), and `X.args`, the argument vector.

A call to `@f` calls the term bound by `with @f := t`, which may use the binders; without a
binding, a `Func` named `f` in scope is called as `f.call`.
-/

namespace LeanMLIR.RIR

open Lean Elab Command Term MLIR

/-- `@f := t`: calls to `@f` call `t`. -/
public syntax calleeBinding := "@" ident " := " term

public meta section

namespace MlirDef

/-! ## Terms -/

def num (n : Nat) : TSyntax `term :=
  ⟨Syntax.mkNumLit (toString n)⟩

/-- `v` as a numeral, negated if `v < 0`. -/
def intLit (v : Int) : CommandElabM (TSyntax `term) :=
  if v < 0 then `(-$(num v.natAbs)) else pure (num v.toNat)

def tyStx : Ty → CommandElabM (TSyntax `term)
  | .bv w => `(.bv $(num w))
  | .ptr => `(.ptr)
  | .vec l w => `(.vec $(num l) $(num w))

def tysStx (ts : List Ty) : CommandElabM (TSyntax `term) := do
  `([$(← ts.toArray.mapM tyStx),*])

/-- The value registers' types, and `hty`, the lemma that proves them. -/
structure ValTys where
  hty : Ident
  vals : List Ty

/-- `Γ.ty i = t` for value register `i` of type `t`: `hty i t rfl`. -/
def ValTys.proof (tys : ValTys) (i : Nat) : CommandElabM (TSyntax `term) := do
  `($(tys.hty) $(num i) $(← tyStx ((tys.vals[i]?).getD (.bv 0))) rfl)

def regStx (tys : ValTys) : RegRef → CommandElabM (TSyntax `term)
  | .arg i => `((.arg $(num i) rfl))
  | .val i => do
    `((.val $(num i) $(← tys.proof i)))

def dstStx (tys : ValTys) (i : Nat) : CommandElabM (TSyntax `term) := do
  `(⟨$(num i), $(← tys.proof i)⟩)

/-- The trie literal. -/
def treeStx : TyTree → CommandElabM (TSyntax `term)
  | .leaf t => do
    `(.leaf $(← tyStx t))
  | .node l r => do
    `(.node $(← treeStx l) $(← treeStx r))

/-- The least `d` with `n ≤ 2 ^ d`. -/
def depth (n : Nat) : Nat :=
  if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- `.cons x₀ (.cons x₁ … .nil)`. -/
def consStx (xs : List (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  xs.foldrM (init := ← `(.nil)) fun x acc => `((.cons $x $acc))

def flagsStx (f : OverflowFlags) : CommandElabM (TSyntax `term) :=
  match f.nsw, f.nuw with
  | false, false => `({})
  | true, false => `({ nsw := true })
  | false, true => `({ nuw := true })
  | true, true => `({ nsw := true, nuw := true })

def boolStx (b : Bool) : CommandElabM (TSyntax `term) :=
  if b then `(true) else `(false)

def predStx : IntPred → CommandElabM (TSyntax `term)
  | .eq => `(.eq)
  | .ne => `(.ne)
  | .slt => `(.slt)
  | .sle => `(.sle)
  | .sgt => `(.sgt)
  | .sge => `(.sge)
  | .ult => `(.ult)
  | .ule => `(.ule)
  | .ugt => `(.ugt)
  | .uge => `(.uge)

def unOpStx : UnOp t₁ t → CommandElabM (TSyntax `term)
  | .gepConst n => `((.gepConst $(num n)))
  | .trunc f => do
    `((.trunc $(← flagsStx f)))
  | .zext nneg => do
    `((.zext $(← boolStx nneg)))
  | .sext => do
    `((.sext))
  | .bswap => `(.bswap)
  | .bitcast (t := t) (t' := t') _ => do
    `((.bitcast (t := $(← tyStx t)) (t' := $(← tyStx t')) rfl))

def binOpStx : BinOp t₁ t₂ t → CommandElabM (TSyntax `term)
  | .and => `(.and)
  | .or d => do
    `((.or $(← boolStx d)))
  | .xor => `(.xor)
  | .add f => do
    `((.add $(← flagsStx f)))
  | .sub f => do
    `((.sub $(← flagsStx f)))
  | .mul f => do
    `((.mul $(← flagsStx f)))
  | .shl f => do
    `((.shl $(← flagsStx f)))
  | .lshr e => do
    `((.lshr $(← boolStx e)))
  | .ashr e => do
    `((.ashr $(← boolStx e)))
  | .smin => `(.smin)
  | .icmp p => do
    `((.icmp $(← predStx p)))
  | .vector op => do
    `((.vector $(← binOpStx op)))
  | .extractelement => `(.extractelement)
  | .shufflevector (l₁ := l₁) (l₂ := l₂) idx => do
    let lanes ←
      idx.toArray.mapM fun
          | some k => `(some $(num k.val))
          | none => `(none)
    `((.shufflevector (#v[$lanes,*] : Vector (Option (Fin (2 * $(num l₁)))) $(num l₂))))

def ternOpStx : TernOp t₁ t₂ t₃ t → CommandElabM (TSyntax `term)
  | .select => `(.select)
  | .insertelement => `(.insertelement)
  | .vpermi2var => `(.vpermi2var)
  | .vpmadd52l => `(.vpmadd52l)
  | .vpmadd52h => `(.vpmadd52h)
  | .fshl => `(.fshl)
  | .fshr => `(.fshr)
  | .vector op => do
    `((.vector $(← ternOpStx op)))

def constStx : ConstLit → CommandElabM (TSyntax `term)
  | .bv w v => do
    `(($(← intLit v) : BitVec $(num w)))
  | .vec l w vs => do
    `((#v[$(← vs.toArray.mapM intLit),*] : Vector (BitVec $(num w)) $(num l)))
  | .splat l w v => do
    `((.replicate $(num l) $(← intLit v) : Vector (BitVec $(num w)) $(num l)))

/-- The instruction, calling `callee f` for `@f`. -/
def instrStx (tys : ValTys) (callee : String → TSyntax `term) :
    PInstr → CommandElabM (TSyntax `term)
  | .const c d => do
    `(.const $(← constStx c) $(← dstStx tys d))
  | .poison _ d => do
    `(.poison $(← dstStx tys d))
  | .unop op d a => do
    `(.unop $(← unOpStx op) $(← dstStx tys d) $(← regStx tys a))
  | .binop op d a b => do
    `(.binop $(← binOpStx op) $(← dstStx tys d) $(← regStx tys a) $(← regStx tys b))
  | .ternop op d a b c => do
    `(.ternop $(← ternOpStx op) $(← dstStx tys d) $(← regStx tys a) $(← regStx tys b)
          $(← regStx tys c))
  | .load _ d p => do
    `(.load $(← dstStx tys d) $(← regStx tys p))
  | .store _ p v => do
    `(.store $(← regStx tys p) $(← regStx tys v))
  | .memset _ dst v l => do
    `(.memset $(← regStx tys dst) $(← regStx tys v) $(← regStx tys l))
  | .memcpy _ dst src l => do
    `(.memcpy $(← regStx tys dst) $(← regStx tys src) $(← regStx tys l))
  | .alloca d n => do
    `(.alloca $(← dstStx tys d) $(num n))
  | .lifetimeStart p n => do
    `(.lifetimeStart $(← regStx tys p) $(num n))
  | .lifetimeEnd p n => do
    `(.lifetimeEnd $(← regStx tys p) $(num n))
  | .call f _ _ args rets => do
    `(.call $(callee f) $(← consStx (← args.mapM (regStx tys)))
          $(← consStx (← rets.mapM (dstStx tys))))

def jumpStx (tys : ValTys) (j : PJump) : CommandElabM (TSyntax `term) := do
  `(⟨$(num j.target), $(← consStx (← j.args.mapM (regStx tys)))⟩)

def exitStx (tys : ValTys) : PExit → CommandElabM (TSyntax `term)
  | .ret vs => do
    `(.ret $(← consStx (← vs.mapM (regStx tys))))
  | .br j => do
    `(.br $(← jumpStx tys j))
  | .condBr c t f => do
    `(.condBr $(← regStx tys c) $(← jumpStx tys t) $(← jumpStx tys f))
  | .switch w v d cs => do
    let cs ←
      cs.toArray.mapM fun (c, j) => do
          let c ←
            if c < 0 then
              `(BitVec.ofInt $(num w) $(← intLit c))
            else
              `(BitVec.ofNat $(num w) $(num c.toNat))
          `(($c, $(← jumpStx tys j)))
    `(.switch $(← regStx tys v) $(← jumpStx tys d) [$cs,*])

/-! ## Callees and binders -/

/-- The identifiers in `stx`. -/
partial def idents (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n.eraseMacroScopes]
  | .node _ _ args => args.flatMap idents
  | _ => #[]

/-- The term a call to `@name` calls: the binding's, or `name.call` for a `Func` named `name`. -/
def calleeTerm (ref : Syntax) (table : List (String × TSyntax `term)) (name : String) :
    CommandElabM (TSyntax `term) := do
  if let some t := table.lookup name then
    return t
  let candidates ←
    try
      liftCoreM (resolveGlobalName name.toName)
    catch _ =>
      pure []
  for (c, fields) in candidates do
    if fields.isEmpty then
      if let some info := (← getEnv).find? c then
        if info.type == Lean.mkConst ``Func then
          return ← `($(mkIdent c).call)
  throwErrorAt ref "llvm.call to @{name}: no callee bound; add `with @{name} := …`, or define a \
    `{name} : Func`"

/-- Check that `t` has the type the calls to `@name` need, under the binders. -/
def checkCallee (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (name : String)
    (t : TSyntax `term) (ts us : List Ty) : CommandElabM Unit := do
  let expected ← `(Vals $(← tysStx ts) → EffectM (Vals $(← tysStx us)))
  runTermElabM fun _ =>
      Term.elabBinders binders fun _ => do
        let ty ← Term.elabType expected
        let e ← Term.elabTerm t ty
        Term.synthesizeSyntheticMVarsNoPostponing
        let ety ← Meta.inferType e
        unless ← Meta.isDefEq ety ty do
          throwErrorAt t "@{name}: the call sites need a callee of type{indentExpr ty}\nbut the \
        term has type{indentExpr ety}"

end MlirDef

open MlirDef in
/-- Define `x` from the region, as described in the module docstring. -/
def elabMlirDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (x : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (r : TSyntax `mlir_region) (callees : Array (TSyntax ``calleeBinding)) :
    CommandElabM Unit := do
  let rgn ← liftCoreM (region r)
  let p ← match Prog.ofRegion rgn with
    | .ok p => pure p
    | .error e => throwErrorAt r e
  let table ← callees.toList.mapM fun (c : TSyntax ``calleeBinding) => match c with
    | `(calleeBinding| @$f:ident := $t) => pure (f.getId.toString, t)
    | c => throwErrorAt c "malformed callee binding"
  -- every callee's term, checked against its call sites
  let calls := p.blocks.flatMap fun b => b.body.filterMap fun
    | .call f ts us _ _ => some (f, ts, us)
    | _ => none
  let mut terms : List (String × TSyntax `term) := []
  for (f, ts, us) in calls do
    if (terms.lookup f).isNone then
      let t ← calleeTerm r table f
      checkCallee binders f t ts us
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
      | _ => []
    let keep := (binders.zip binderNames).filter fun (_, ns) => ns.any used.contains
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
    let Γdef ←
      -- the kernel checks the count: the elaborator would recurse once per value
      `(abbrev $Γ : Ctx :=
          ⟨$(num p.Γ.n), $(← tysStx p.Γ.args), $(← tysStx p.Γ.vals), by decide +kernel⟩)
    let d := depth p.Γ.n
    let treeDef ← `(abbrev $tree : TyTree := $(← treeStx (TyTree.ofList d p.Γ.vals)))
    -- the kernel checks the trie against `Γ.vals` once
    let htyDef ←
      `(theorem $(tys.hty) (k : Fin ($Γ).n) (t : Ty) (h : ($tree).get k = t) : ($Γ).ty k = t :=
          (Ctx.ty_eq_get (d := $(num d)) (by decide +kernel) (by decide) k).trans h)
    let tysDef ←
      if n == 1 then `(abbrev $blockTys : Fin 1 → List Ty := fun _ => [])
      else
        let alts ← (fins.zip p.blocks).filterMapM fun (k, b) => do
          if b.params.isEmpty then return none
          let tys ← tysStx (paramTys b)
          return some (← `(Lean.Parser.Term.matchAltExpr| | ⟨$(num k), _⟩ => $tys))
        let alts := alts.toArray.push (← `(Lean.Parser.Term.matchAltExpr| | _ => []))
        `(abbrev $blockTys : Fin $(num n) → List Ty := fun $alts:matchAlt*)
    let paramsDef ←
      if n == 1 then
        `(abbrev $blockParams : (k : Fin 1) → Dsts $Γ ($blockTys k) := fun _ => .nil)
      else
        let alts ← (fins.zip p.blocks).toArray.mapM fun (k, b) => do
          let ds ← consStx (← b.params.mapM (dstStx tys))
          `(Lean.Parser.Term.matchAltExpr| | ⟨$(num k), _⟩ => $ds)
        `(abbrev $blockParams : (k : Fin $(num n)) → Dsts $Γ ($blockTys k) :=
            fun $alts:matchAlt*)
    let blockDefs ← p.blocks.toArray.mapM fun b => do
      let (bs, _) := blockBinders b
      let body ← b.body.toArray.mapM (instrStx tys callee)
      `(def $(blockName b) $bs* : BasicBlock $Γ $tRets $blockTys :=
          { body := [$body,*], exit := $(← exitStx tys b.exit) })
    let blocksVal ←
      if let [b] := p.blocks then `(fun _ => $(blockName b) $((blockBinders b).2)*)
      else
        let alts ← (fins.zip p.blocks).toArray.mapM fun (k, b) => do
          let (_, args) := blockBinders b
          `(Lean.Parser.Term.matchAltExpr| | ⟨$(num k), _⟩ => $(blockName b) $args*)
        `(fun $alts:matchAlt*)
    let funcDef ←
      `($[$doc?:docComment]? @[reducible] def $x $binders* : Func :=
          { Γ := $Γ, tRets := $tRets, n := $(num n), blockTys := $blockTys,
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

/-- `mlir_def X binders := { region } with @f := t, …`: define `X : Func` and its pieces from a
generic-form MLIR region. -/
syntax (name := mlirDef) (docComment)? "mlir_def " ident (ppSpace bracketedBinder)* " := "
  mlir_region (" with " calleeBinding,+)? : command

elab_rules : command
  | `($[$doc?:docComment]? mlir_def $x:ident $bs* := $r:mlir_region $[with $cs,*]?) =>
    elabMlirDef doc? x bs r ((cs.map (·.getElems)).getD #[])

/-- `mlir_region% { region }` is the region's AST, a `MLIR.Region`: `translate`'s input. -/
elab "mlir_region% " r:mlir_region : term => do
  return toExpr (← MLIR.region r)

end LeanMLIR.RIR

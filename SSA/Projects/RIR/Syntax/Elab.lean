module

public import SSA.Projects.RIR.Syntax.Parser
public import SSA.Projects.RIR.Syntax.Translate
public import SSA.Projects.RIR.Semantics.Func
public meta import SSA.Projects.RIR.Syntax.Parser
public meta import SSA.Projects.RIR.Syntax.Translate
public meta import Lean.Elab.Command

/-!
# `mlir_def`

`mlir_def X binders := { region } with @f := t, …` translates a generic-form MLIR region and
defines it in the shape of a hand lift:
* `X.Γ`, `X.blockTys`, `X.blockParams` (`abbrev`s);
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

/-- From this many values on, an index is written `(k : Fin n)`: a bare `k` unfolds
`Γ.vals.length` and hits `maxRecDepth`. -/
def finLitLimit : Nat :=
  100

/-- Value index `i` of `n`. -/
def valIdx (n i : Nat) : CommandElabM (TSyntax `term) :=
  if n < finLitLimit then pure (num i) else `(($(num i) : Fin $(num n)))

def regStx (n : Nat) : RegRef → CommandElabM (TSyntax `term)
  | .arg i => `((.arg $(num i) rfl))
  | .val i => do
    `((.val $(← valIdx n i) rfl))

def dstStx (n i : Nat) : CommandElabM (TSyntax `term) := do
  `(⟨$(← valIdx n i), rfl⟩)

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
  | .shufflevector (l := l) idx => do
    let lanes ←
      idx.toArray.mapM fun
          | some k => `(some $(num k.val))
          | none => `(none)
    `((.shufflevector (#v[$lanes,*] : Vector (Option (Fin (2 * $(num l)))) $(num l))))

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

/-- The instruction, calling `callee f` for `@f`; `nv` is the number of values. -/
def instrStx (nv : Nat) (callee : String → TSyntax `term) : PInstr → CommandElabM (TSyntax `term)
  | .const c d => do
    `(.const $(← constStx c) $(← dstStx nv d))
  | .poison _ d => do
    `(.poison $(← dstStx nv d))
  | .unop op d a => do
    `(.unop $(← unOpStx op) $(← dstStx nv d) $(← regStx nv a))
  | .binop op d a b => do
    `(.binop $(← binOpStx op) $(← dstStx nv d) $(← regStx nv a) $(← regStx nv b))
  | .ternop op d a b c => do
    `(.ternop $(← ternOpStx op) $(← dstStx nv d) $(← regStx nv a) $(← regStx nv b) $(← regStx nv c))
  | .load _ d p => do
    `(.load $(← dstStx nv d) $(← regStx nv p))
  | .store _ p v => do
    `(.store $(← regStx nv p) $(← regStx nv v))
  | .memset _ dst v l => do
    `(.memset $(← regStx nv dst) $(← regStx nv v) $(← regStx nv l))
  | .memcpy _ dst src l => do
    `(.memcpy $(← regStx nv dst) $(← regStx nv src) $(← regStx nv l))
  | .alloca d n => do
    `(.alloca $(← dstStx nv d) $(num n))
  | .lifetimeStart p n => do
    `(.lifetimeStart $(← regStx nv p) $(num n))
  | .lifetimeEnd p n => do
    `(.lifetimeEnd $(← regStx nv p) $(num n))
  | .call f _ _ args rets => do
    `(.call $(callee f) $(← consStx (← args.mapM (regStx nv)))
          $(← consStx (← rets.mapM (dstStx nv))))

def jumpStx (nv : Nat) (j : PJump) : CommandElabM (TSyntax `term) := do
  `(⟨$(num j.target), $(← consStx (← j.args.mapM (regStx nv)))⟩)

def exitStx (nv : Nat) : PExit → CommandElabM (TSyntax `term)
  | .ret vs => do
    `(.ret $(← consStx (← vs.mapM (regStx nv))))
  | .br j => do
    `(.br $(← jumpStx nv j))
  | .condBr c t f => do
    `(.condBr $(← regStx nv c) $(← jumpStx nv t) $(← jumpStx nv f))
  | .switch w v d cs => do
    let cs ←
      cs.toArray.mapM fun (c, j) => do
          let c ←
            if c < 0 then
              `(BitVec.ofInt $(num w) $(← intLit c))
            else
              `(BitVec.ofNat $(num w) $(num c.toNat))
          `(($c, $(← jumpStx nv j)))
    `(.switch $(← regStx nv v) $(← jumpStx nv d) [$cs,*])

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
  let blockName (b : PBlock) : Ident := name (if n == 1 then `entry else .mkSimple b.name)
  let tRets ← tysStx p.tRets
  let nv := p.Γ.vals.length
  let cmds ← do
    let paramTys (b : PBlock) := b.params.map fun i => (p.Γ.vals[i]?).getD (.bv 0)
    let fins := List.range n
    let Γdef ←
      `(abbrev $Γ : Ctx := ⟨$(← tysStx p.Γ.args), $(← tysStx p.Γ.vals)⟩)
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
          let ds ← consStx (← b.params.mapM (dstStx nv))
          `(Lean.Parser.Term.matchAltExpr| | ⟨$(num k), _⟩ => $ds)
        `(abbrev $blockParams : (k : Fin $(num n)) → Dsts $Γ ($blockTys k) :=
            fun $alts:matchAlt*)
    let blockDefs ← p.blocks.toArray.mapM fun b => do
      let (bs, _) := blockBinders b
      let body ← b.body.toArray.mapM (instrStx nv callee)
      `(def $(blockName b) $bs* : BasicBlock $Γ $tRets $blockTys :=
          { body := [$body,*], exit := $(← exitStx nv b.exit) })
    let blocksVal ←
      if let [b] := p.blocks then `(fun _ => $(blockName b))
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
    pure (#[Γdef, tysDef, paramsDef] ++ blockDefs ++ #[funcDef, argsDef])
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

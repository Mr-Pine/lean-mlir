module

public import MLIR.Syntax.Parser
public import MLIR.Syntax.Translate
public import MLIR.Semantics.Func
public import MLIR.Semantics.GlobalInitializer
public import MLIR.TyTree
public meta import MLIR.Syntax.Parser
public meta import MLIR.Syntax.Translate
public meta import MLIR.TyTree
public meta import Lean.Elab.Command
public meta import Lean.Meta.Reduce

/-!
# `mlir_def`

`mlir_def X binders := { region } with @f := t, …` translates a generic-form MLIR region, or a
whole `"llvm.func"` with the aliases it refers to (its attributes checked by
`Translate.checkFuncAttrs`), and defines it in the shape of a hand lift:
* `X.Γ`, `X.tree`, `X.blockTys`, `X.blockParams` (`abbrev`s), and `X.hty`, which proves a value
  register's type from `X.tree`;
* one `def` per block: `X.entry` for a single block, else `X.bb0`, `X.bb1`, … by MLIR name;
* `X : Func` (`@[reducible]`), and `X.args`, the argument vector.

The block bodies name value registers by `rir_reg%`/`rir_dst%`, whose types the kernel alone
checks.

A call to `@f` calls `t.call` for the `Func` bound by `with @f := t`, or `t` for a function of the
call's type (with a warning: no lifted region backs it); an `llvm.mlir.addressof`
of `@g` stores the value of the `GlobalInitializer` bound by `with @g := t` in a fresh block and
returns its address. The terms may use the binders. Every called or addressed symbol needs a
binding, and a symbol cannot be both.
-/

namespace MLIR

open Lean Elab Command Term MLIR

/-- `@f := t`: calls to `@f` call the `Func` `t`; addresses of `@f` are of the
`GlobalInitializer` `t`'s value. -/
public syntax calleeBinding := "@" ident " := " term

/-- `rir_reg% X.hty k : Reg X.Γ t`: value register `k` of the `mlir_def` `X`, of the type `t` at
entry `k` of `X.tree`; only the kernel checks the type. -/
syntax (name := rirReg) "rir_reg% " ident num : term

/-- `rir_dst% X.hty k : Dst X.Γ t`: `rir_reg% X.hty k` as a destination. -/
syntax (name := rirDst) "rir_dst% " ident num : term

/-- `rir_ty% X.hty k`: the type `t` of `rir_reg% X.hty k`. -/
syntax (name := rirTy) "rir_ty% " ident num : term

/-- `rir_rfl%`: `rfl` at the expected type, which only the kernel checks. -/
syntax (name := rirRfl) "rir_rfl%" : term

/-- `rir_tys% [t, …]`: the `List Ty` literal of the type literals `t, …`, built without
elaborating them. -/
syntax (name := rirTys) "rir_tys% " "[" term,* "]" : term

/-- `rir_tree% d [t, …]`: the literal of `TyTree.ofList d [t, …]`, as `rir_tys%`. -/
syntax (name := rirTree) "rir_tree% " num " [" term,* "]" : term

public meta section

namespace MlirDef

/-! ## Terms -/

def numLit (n : Nat) : NumLit :=
  Syntax.mkNumLit (toString n)

def num (n : Nat) : TSyntax `term :=
  ⟨numLit n⟩

/-- `v` as a numeral, negated if `v < 0`. -/
def intLit (v : Int) : CommandElabM (TSyntax `term) :=
  if v < 0 then `(-$(num v.natAbs)) else pure (num v.toNat)

def tyStx : Ty → CommandElabM (TSyntax `term)
  | .bv w => `(.bv $(num w))
  | .ptr => `(.ptr)
  | .vec l w => `(.vec $(num l) $(num w))
  | .array n t => do
    `(.array $(num n) $(← tyStx t))
  | .struct fields => do
    let fs ← fields.attach.mapM fun ⟨f, _⟩ => tyStx f
    `(.struct [$(fs.toArray),*])

def tysStx (ts : List Ty) : CommandElabM (TSyntax `term) := do
  `([$(← ts.toArray.mapM tyStx),*])

/-- `hty`, the lemma that proves the value registers' types. -/
structure ValTys where
  hty : Ident

def regStx (tys : ValTys) : RegRef → CommandElabM (TSyntax `term)
  | .arg i => `((.arg $(num i) rfl))
  | .val i => `((rir_reg% $(tys.hty) $(numLit i)))

def dstStx (tys : ValTys) (i : Nat) : CommandElabM (TSyntax `term) :=
  `((rir_dst% $(tys.hty) $(numLit i)))

/-- The type `t` of register `r`: a lookup for a value register. -/
def ValTys.tyStx (tys : ValTys) (t : Ty) : RegRef → CommandElabM (TSyntax `term)
  | .arg _ => MlirDef.tyStx t
  | .val i => `((rir_ty% $(tys.hty) $(numLit i)))

/-- The type `tyStx` writes as `stx`. -/
partial def tyOfStx (stx : Term) : Option Ty :=
  match stx with
  | `(.bv $w:num) => some (.bv w.getNat)
  | `(.ptr) => some .ptr
  | `(.vec $l:num $w:num) => some (.vec l.getNat w.getNat)
  | `(.array $n:num $t) => (.array n.getNat ·) <$> tyOfStx t
  | `(.struct [$ts,*]) => .struct <$> ts.getElems.toList.mapM tyOfStx
  | _ => none

/-- The types `tyStx` writes as `ts`. -/
def tysOfStx (ts : Array Term) : MetaM (List Ty) :=
  ts.toList.mapM fun t => do
    let some t := tyOfStx t | throwErrorAt t "expected a type literal"
    return t

/-- The trie literal's expression. -/
def treeExpr : TyTree → Expr
  | .leaf t => mkApp (mkConst ``TyTree.leaf) (toExpr t)
  | .node l r => mkApp2 (mkConst ``TyTree.node) (treeExpr l) (treeExpr r)

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
  | .gepConst n => do
    `((.gepConst $(← intLit n)))
  | .trunc f => do
    `((.trunc $(← flagsStx f)))
  | .zext nneg => do
    `((.zext $(← boolStx nneg)))
  | .sext => do
    `((.sext))
  | .bswap => `(.bswap)
  | .cttz z => do
    `((.cttz $(← boolStx z)))
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
  | .ptrcmp ne => do
    `((.ptrcmp $(← boolStx ne)))
  | .gepDyn byteOff stride => `((.gepDyn $(num byteOff) $(num stride)))
  | .vector op => do
    `((.vector $(← binOpStx op)))
  | .extractelement => `(.extractelement)
  | .shufflevector (l₁ := l₁) (l₂ := l₂) idx => do
    let lanes ←
      idx.toArray.mapM fun
          | some k => `(some $(num k.val))
          | none => `(none)
    `((.shufflevector (#v[$lanes,*] : Vector (Option (Fin (2 * $(num l₁)))) $(num l₂))))
  | .insertvalue indices tCont tVal _ => do
    `((.insertvalue [$(indices.toArray.map num),*] $(← tyStx tCont) $(← tyStx tVal) rir_rfl%))

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

mutual
/-- `c`, a term of type `⟦c.ty⟧ᵣ`. -/
partial def constStx : ConstLit → CommandElabM (TSyntax `term)
  | .bv w v => do
    `(($(← intLit v) : BitVec $(num w)))
  | .vec l w vs => do
    `((#v[$(← vs.toArray.mapM intLit),*] : Vector (BitVec $(num w)) $(num l)))
  | .splat l w v => do
    `((.replicate $(num l) $(← intLit v) : Vector (BitVec $(num w)) $(num l)))
  | .array n w vs => do
    `((#v[$(← vs.toArray.mapM intLit),*] : Vector (BitVec $(num w)) $(num n)))
  | .arraySplat n w v => do
    `((.replicate $(num n) $(← intLit v) : Vector (BitVec $(num w)) $(num n)))
  | .null => `(Pointer.null)
  | .agg t ms => do
    `(($(← membersStx t ms) : Ty.denoteRaw $(← tyStx t)))
/-- The aggregate of type `t` with members `ms`, unascribed: an array as `#v[…]`, a struct as the
tuple of its fields. -/
partial def membersStx (t : Ty) (ms : List ConstLit) : CommandElabM (TSyntax `term) := do
  let ms ←
    ms.toArray.mapM fun
        | .agg t ms => membersStx t ms
        | c => constStx c
  match t, ms with
  | .array .., ms =>
    `(#v[$ms,*])
  | .struct _, #[] =>
    `(())
  | .struct _, #[m] =>
    pure m
  | .struct _, ms =>
    `(($(ms[0]!), $(ms.extract 1),*))
  | t, _ =>
    throwError "an aggregate of type {t.toMLIR}"
end

/-- The instruction, calling `callee f` for `@f` or loading `global g` for `@g`. -/
def instrStx (tys : ValTys) (callee : String → TSyntax `term) (global : String → TSyntax `term) :
    PInstr → CommandElabM (TSyntax `term)
  | .const c d => do
    `(.const (τ := $(← tys.tyStx c.ty (.val d))) $(← constStx c) $(← dstStx tys d))
  | .poison _ d => do
    `(.poison $(← dstStx tys d))
  | .unop op d a => do
    `(.unop $(← unOpStx op) $(← dstStx tys d) $(← regStx tys a))
  | .binop (.insertvalue indices tCont tVal _) d a b => do
    `(.binop
          (.insertvalue [$(indices.toArray.map num),*] $(← tys.tyStx tCont (.val d))
            $(← tys.tyStx tVal b) rir_rfl%)
          $(← dstStx tys d) $(← regStx tys a) $(← regStx tys b))
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
  | .addressof g d => do
    `(.addressof $(global g) $(← dstStx tys d))

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

/-- The term bound to `@name`. -/
def calleeTerm (ref : Syntax) (table : List (String × TSyntax `term)) (name : String) :
    CommandElabM (TSyntax `term) := do
  let some t := table.lookup name
    | throwErrorAt ref "llvm.call to @{name}: no callee bound; add `with @{name} := …`"
  return t

/-- The callee term for `t`, bound to `@name`: `t.call` for a `Func` whose `call` has the type the
calls need, under the binders; or `t` itself for a function of that type, with a warning. -/
def checkCallee (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (name : String)
    (t : TSyntax `term) (ts us : List Ty) : CommandElabM (TSyntax `term) := do
  let expected ← `(Vals $(← tysStx ts) → EffectM (Vals $(← tysStx us)))
  let isFunc ←
    runTermElabM fun _ =>
        Term.elabBinders binders fun _ => do
          let ty ← Term.elabType expected
          let g ← Term.elabTerm t none
          Term.synthesizeSyntheticMVarsNoPostponing
          let gty ← Meta.inferType g
          if (← Meta.whnfR gty).isConstOf ``Func then
            let ety ← Meta.inferType (mkApp (mkConst ``Func.call) g)
            unless ← Meta.isDefEq ety ty do
              -- `g.Γ.args` and `g.tRets` as lists
              let args ← Meta.mkAppM ``Ctx.args #[← Meta.mkAppM ``Func.Γ #[g]]
              let rets ← Meta.mkAppM ``Func.tRets #[g]
              let (args', rets') := (← Meta.reduce args, ← Meta.reduce rets)
              let ety :=
                (← instantiateMVars ety).replace fun e =>
                  if e == args then some args' else if e == rets then some rets' else none
              throwErrorAt t "@{name}: the call sites need a callee of type{indentExpr ty}\nbut \
          `{t}.call` has type{indentExpr ety}"
            return true
          unless ← Meta.isDefEq gty ty do
            throwErrorAt t "@{name}: expected a `Func`, or a function of type{indentExpr ty}\nbut \
        `{t}` has type{indentExpr gty}"
          logWarningAt t
              m!"@{name} is bound to a function, not a `Func`: the calls run it as given, \
          not a lifted region"
          return false
  if isFunc then
    `(($t).call)
  else
    `(($t))

/-- The `GlobalInitializer` bound to `@name`. -/
def globalTerm (ref : Syntax) (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (table : List (String × TSyntax `term)) (name : String) : CommandElabM (TSyntax `term) := do
  let some t := table.lookup name
    | throwErrorAt ref "addressof of @{name}: no global initializer bound; add `with @{name} := …`"
  runTermElabM fun _ =>
      Term.elabBinders binders fun _ => do
        discard <| Term.elabTermEnsuringType t (mkConst ``GlobalInitializer)
        Term.synthesizeSyntheticMVarsNoPostponing
  return t

/-! ## Value registers -/

/-- Entry `k` of the trie literal `e`, as `TyTree.get` reads it. -/
partial def treeGet? (e : Expr) (k : Nat) : Option Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``TyTree.leaf, #[t]) => some t
  | (``TyTree.node, #[l, r]) => treeGet? (if k % 2 = 0 then l else r) (k / 2)
  | _ => none

/-- Value register `k` of a `mlir_def`, read off its literals. -/
structure ValTy where
  /-- `hty : ∀ (k : Fin Γ.n) (t : Ty), tree.get k = t → Γ.ty k = t` -/
  hty : Name
  Γ : Expr
  /-- `Fin Γ.n` -/
  fin : Expr
  /-- `tree.get k = t`, over `k t` -/
  get : Expr
  /-- The register's type: entry `k` of `tree`'s literal. -/
  t : Expr

/-- Value register `k` of the `mlir_def` whose type lemma is `hty`. -/
def valTy (hty : Ident) (k : Nat) : TermElabM ValTy := do
  let h ← resolveGlobalConstNoOverload hty
  -- the statement only: the proof may still be checked
  let some (Γ, fin, get, tree) :=
    (match (← getConstVal h).type with
    | .forallE _ fin (.forallE _ _ (.forallE _ get _ _) _) _ => do
      let (``Fin, #[n]) := fin.getAppFnArgs | none
      let (``Ctx.n, #[Γ]) := n.getAppFnArgs | none
      let (``Eq, #[_, lhs, _]) := get.getAppFnArgs | none
      let (``TyTree.get, #[.const tree _, _]) := lhs.getAppFnArgs | none
      some (Γ, fin, get, tree)
    | _ => none)
    | throwErrorAt hty "{h} does not state `∀ k t, tree.get k = t → Γ.ty k = t`"
  let env := (← getEnv).setExporting false
  let value? (e : Expr) := e.constName? >>= env.find? >>= (·.value?) |>.map (·.consumeMData)
  let some n := value? Γ >>= (·.getAppArgs[0]?) >>= (·.nat?)
    | throwErrorAt hty "{Γ} is not a context literal"
  unless k < n do
    throwErrorAt hty "{Γ} has no value register {k}, only {n}"
  let some t := value? (.const tree []) >>= (treeGet? · k)
    | throwErrorAt hty "{tree} is not a type trie literal"
  return { hty := h, Γ, fin, get, t }

/-- `rir_reg% hty k`'s `Γ`, type `t`, index `k : Fin Γ.n`, and `hty k t rfl : Γ.ty k = t`, where
only the kernel checks `rfl`. -/
def valReg (hty : Ident) (k : Nat) : TermElabM (Expr × Expr × Expr × Expr) := do
  let { hty, Γ, fin, get, t } ← valTy hty k
  let i ← Meta.mkNumeral fin k
  let rfl :=
    Meta.mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Ty) t)
      (get.instantiateRev #[i, t])
  return (Γ, t, i, mkApp3 (mkConst hty) i t rfl)

end MlirDef

open MlirDef in
/-- A match over `Fin n` by its literals `⟨0, _⟩ … ⟨n - 1, _⟩`, with an impossible last arm
`⟨k + n, h⟩` from `16` arms on, where Lean's exhaustiveness check no longer finds it empty; below
that, as Lean compiles the plain match. -/
def finAlts (n : Nat) (alts : Array (TSyntax ``Lean.Parser.Term.matchAlt)) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
  if n < 16 then
    return alts
  return alts.push (← `(Lean.Parser.Term.matchAltExpr| | ⟨_ + $(num n), h⟩ => absurd h (by omega)))

/-- Elaborate a lift's definitions, as in a `noncomputable section` if `nc`: then those the code
generator cannot compile (a long table's) are noncomputable, the others not. -/
def elabLift (nc : Bool) (cmds : Array Syntax) : CommandElabM Unit :=
  if nc then
    withScope ({ · with isNoncomputable := true }) do
      for c in cmds do
        elabCommand c
  else
    for c in cmds do
      elabCommand c

open MlirDef in
/-- Define `x` from the region, as described in the module docstring. -/
def elabMlirDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (nc : Bool) (x : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (r : Syntax) (rgn : Region) (callees : Array (TSyntax ``calleeBinding)) :
    CommandElabM Unit := do
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
      terms := terms ++ [(f, ← checkCallee binders f t ts us)]

  -- every global's term, checked to be a `GlobalInitializer`
  let addrs := p.blocks.flatMap fun b => b.body.filterMap fun
    | .addressof g _ => some g
    | _ => none
  let mut globals : List (String × TSyntax `term) := []
  for g in addrs do
    if (terms.lookup g).isSome then
      throwErrorAt r "@{g} is both called and its address taken"
    if (globals.lookup g).isNone then
          let t ← globalTerm r binders table g
          globals := globals ++ [(g, ← `(($t).value))]

  for (f, _) in table do
    unless (terms.lookup f).isSome || (globals.lookup f).isSome do
      logWarning m!"@{f} is bound but never called or loaded"
  let callee (f : String) : TSyntax `term := (terms.lookup f).getD (mkIdent (.mkSimple f))
  let global (g : String) : TSyntax `term := (globals.lookup g).getD (mkIdent (.mkSimple g))
  -- the binders each block needs: those its callees' terms mention
  let binderNames ← binders.mapM fun b => getBracketedBinderIds b
  let blockBinders (b : PBlock) :
      Array (TSyntax ``Lean.Parser.Term.bracketedBinder) × Array Ident :=
    let used := b.body.flatMap fun
      | .call f .. => (idents (callee f)).toList
      | .addressof g .. => (idents (global g)).toList
      | _ => []
    let keep := (binders.zip binderNames).filter fun (_, ns) => ns.any used.contains
    (keep.map (·.1), keep.flatMap fun (_, ns) => ns.map mkIdent)
  let n := p.blocks.length
  let name (s : Name) : Ident := mkIdent (x.getId ++ s)
  let Γ := name `Γ
  let blockTys := name `blockTys
  let blockParams := name `blockParams
  let tree := name `tree
  let tys : ValTys := { hty := name `hty }
  let blockName (b : PBlock) : Ident := name (if n == 1 then `entry else .mkSimple b.name)
  let tRets ← tysStx p.tRets
  let vals ← p.Γ.vals.toArray.mapM tyStx
  let cmds ← do
    let paramTys (b : PBlock) := b.params.map fun i => (p.Γ.vals[i]?).getD (.bv 0)
    let fins := List.range n
    let Γdef ←
      -- the kernel checks the count: the elaborator would recurse once per value
      `(abbrev $Γ : Ctx :=
          ⟨$(num p.Γ.n), $(← tysStx p.Γ.args), rir_tys% [$vals,*], by decide +kernel,
            $(num p.Γ.argBase), $(num p.Γ.valBase)⟩)
    let d := depth p.Γ.n
    let treeDef ← `(abbrev $tree : TyTree := rir_tree% $(numLit d) [$vals,*])
    -- the kernel checks the trie against `Γ.vals` once
    let htyDef ←
      `(theorem $(tys.hty) (k : Fin ($Γ).n) (t : Ty) (h : ($tree).get k = t) : ($Γ).ty k = t :=
          (Ctx.ty_eq_get (d := $(num d)) rir_rfl% (by decide) k).trans h)
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
            fun $(← finAlts n alts):matchAlt*)
    let blockDefs ← p.blocks.toArray.mapM fun b => do
      let (bs, _) := blockBinders b
      let body ← b.body.toArray.mapM (instrStx tys callee global)
      `(def $(blockName b) $bs* : BasicBlock $Γ $tRets $blockTys :=
          { body := [$body,*], exit := $(← exitStx tys b.exit) })
    let blocksVal ←
      if let [b] := p.blocks then `(fun _ => $(blockName b) $((blockBinders b).2)*)
      else
        let alts ← (fins.zip p.blocks).toArray.mapM fun (k, b) => do
          let (_, args) := blockBinders b
          `(Lean.Parser.Term.matchAltExpr| | ⟨$(num k), _⟩ => $(blockName b) $args*)
        `(fun $(← finAlts n alts):matchAlt*)
    let funcDef ←
      `($[$doc?:docComment]? @[reducible] def $x $binders* : Func :=
          { Γ := $Γ, tRets := $tRets, n := $(num n), blockTys := $blockTys,
            blockParams := $blockParams, hhasBlock := by decide, hentry := rfl,
            blocks := $blocksVal })
    let argNames :=
      (List.range p.Γ.args.length).map fun i => mkIdent (.mkSimple s!"arg{p.Γ.argBase + i}")
    let argBinders ← (argNames.zip p.Γ.args).toArray.mapM fun (a, t) => do
      `(Lean.Parser.Term.bracketedBinderF| ($a : ⟦($(← tyStx t) : Ty)⟧))
    let argsDef ←
      `(def $(name `args) $argBinders* : Vals ($Γ).args := $(← consStx (argNames.map (⟨·.raw⟩))))
    pure (#[Γdef, treeDef, htyDef, tysDef, paramsDef] ++ blockDefs ++ #[funcDef, argsDef])
  elabLift nc cmds

open MlirDef in
/-- Define `x : GlobalInitializer` from a constant global's initializer region, as `mlir_def`
defines a `Func`: `x.Γ`, `x.tree`, `x.hty`, the block `x.entry`, and `x`. A region that builds a
constant (`Prog.constant?`) folds to `x.lit : ⟦x.t⟧ᵣ`, and its block to the one `const x.lit`.
-/
def elabMlirConstDef (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (nc : Bool) (x : Ident)
    (r : Syntax) (rgn : Region) : CommandElabM Unit := do
  let p ← match Prog.ofRegion rgn with
    | .ok p => pure p
    | .error e => throwErrorAt r e
  let [b] := p.blocks | throwErrorAt r "an initializer has exactly one block"
  unless p.Γ.args.isEmpty do
    throwErrorAt r "an initializer takes no arguments"
  let [t] := p.tRets | throwErrorAt r "an initializer returns exactly one value"
  if b.body.any (fun | .call .. | .addressof .. => true | _ => false) then
    throwErrorAt r "an initializer neither calls nor takes addresses"
  let name (s : Name) : Ident := mkIdent (x.getId ++ s)
  let Γ := name `Γ
  let tree := name `tree
  let lit := name `lit
  let c? := p.constant?
  let vals := if c?.isSome then [t] else p.Γ.vals
  -- a folded constant's one register is no value of the region
  let valBase := if c?.isSome then 0 else p.Γ.valBase
  let tys : ValTys := { hty := name `hty }
  let d := depth vals.length
  let tStx ← tyStx t
  let noSymbol (f : String) : TSyntax `term := mkIdent (.mkSimple f)
  let (litDef, body, exit) ←
    match c? with
    | some c =>
      pure
        (#[← `(def $lit : Ty.denoteRaw $tStx := $(← constStx c))],
          #[← `(.const $lit $(← dstStx tys 0))], ← exitStx tys (.ret [.val 0]))
    | none =>
      pure (#[], ← b.body.toArray.mapM (instrStx tys noSymbol noSymbol), ← exitStx tys b.exit)
  let valStxs ← vals.toArray.mapM tyStx
  let cmds ← do
    pure <| #[
      -- the kernel checks the count: the elaborator would recurse once per value
      ← `(abbrev $Γ : Ctx :=
          ⟨$(num vals.length), [], rir_tys% [$valStxs,*], by decide +kernel, 0, $(num valBase)⟩),
      ← `(abbrev $tree : TyTree := rir_tree% $(numLit d) [$valStxs,*]),
      ← `(theorem $(tys.hty) (k : Fin ($Γ).n) (t : Ty) (h : ($tree).get k = t) : ($Γ).ty k = t :=
          (Ctx.ty_eq_get (d := $(num d)) rir_rfl% (by decide) k).trans h)] ++
      litDef ++ #[
      ← `(def $(name `entry) : BasicBlock $Γ [$tStx] (fun _ : Fin 1 => []) :=
          { body := [$body,*], exit := $exit }),
      ← `($[$doc?:docComment]? @[reducible] def $x : GlobalInitializer :=
          { Γ := $Γ, hΓ := rfl, t := $tStx, block := $(name `entry) })]
  elabLift nc cmds

/-- The function `s`'s region, its attributes checked. -/
def funcRegion (s : TSyntax `mlir_symbol) : CommandElabM Region := do
  let op ← liftCoreM (symbolOp s)
  unless op.name == "llvm.func" do
    throwErrorAt s "expected an \"llvm.func\", not \"{op.name}\""
  if let .error e := Translate.checkFuncAttrs op.attrs then
    throwErrorAt s e
  return op.region

/-- The global `s`'s initializer region, its attributes checked. A global given by its `value`
has an empty region; its initializer is then that constant, returned. -/
def globalRegion (s : TSyntax `mlir_symbol) : CommandElabM Region := do
  let op ← liftCoreM (symbolOp s)
  unless op.name == "llvm.mlir.global" do
    throwErrorAt s "expected an \"llvm.mlir.global\", not \"{op.name}\""
  if let .error e := Translate.checkGlobalAttrs op.attrs then
    throwErrorAt s e
  match op.region.blocks, op.attrs.getAttr? "value", op.attrs.getAttr? "global_type" with
  | [{ ops := [], .. }], some v, some (.type t) =>
    let const : Op :=
      { name := "llvm.mlir.constant", res := [("0", t)], args := [], successors := [],
        attrs := .mk [.mk "value" v] }
    let ret : Op :=
      { name := "llvm.return", res := [], args := [("0", t)], successors := [], attrs := .mk [] }
    return ⟨[{ name := "bb0", args := [], ops := [const, ret] }]⟩
  | _, some _, _ => throwErrorAt s "a global has either a `value` or an initializer"
  | _, _, _ => return op.region

end

elab_rules : term <= expectedType
  | `(rir_rfl%) => do
    let expectedType ← tryPostponeIfHasMVars expectedType "rir_rfl%: the expected type is not known"
    let some (_, _, b) := expectedType.eq?
      | throwError "rir_rfl%: expected an equation, not{indentExpr expectedType}"
    return Meta.mkExpectedPropHint (← Meta.mkEqRefl b) expectedType

open MlirDef in
elab_rules : term
  | `(rir_tys% [$ts,*]) => return toExpr (← tysOfStx ts.getElems)
  | `(rir_tree% $d [$ts,*]) => return treeExpr (.ofList d.getNat (← tysOfStx ts.getElems))
  | `(rir_ty% $h $k) => return (← valTy h k.getNat).t
  | `(rir_reg% $h $k) => do
    let (Γ, t, i, h) ← valReg h k.getNat
    return mkApp4 (mkConst ``Reg.val) Γ t i h
  | `(rir_dst% $h $k) => do
    let (Γ, t, i, h) ← valReg h k.getNat
    return mkApp4 (mkConst ``Dst.mk) Γ t i h

/-- `mlir_def X binders := { region } with @f := t, …`: define `X : Func` and its pieces from a
generic-form MLIR region, or an `"llvm.func"`. `noncomputable mlir_def` lets what the code generator cannot compile be
noncomputable, e.g. a function binding a noncomputable global. -/
syntax (name := mlirDef) (docComment)? ("noncomputable ")? "mlir_def " ident
  (ppSpace bracketedBinder)* " := " mlir_region (" with " calleeBinding,+)? : command

@[inherit_doc mlirDef] syntax (name := mlirDefFunc) (docComment)? ("noncomputable ")? "mlir_def "
  ident (ppSpace bracketedBinder)* " := " mlir_symbol (" with " calleeBinding,+)? : command

elab_rules : command
  |
  `(
$[$doc?:docComment]? $[noncomputable%$nc]? mlir_def $x:ident $bs* := $r:mlir_region
      $[with $cs,*]?) =>
    do
    elabMlirDef doc? nc.isSome x bs r (← liftCoreM (region r)) ((cs.map (·.getElems)).getD #[])
  |
  `(
$[$doc?:docComment]? $[noncomputable%$nc]? mlir_def $x:ident $bs* := $f:mlir_symbol
      $[with $cs,*]?) =>
    do
    elabMlirDef doc? nc.isSome x bs f (← funcRegion f) ((cs.map (·.getElems)).getD #[])

/-- `mlir_const_def X := { region }`: define `X : GlobalInitializer` and its pieces from a constant
global's initializer region, or its `"llvm.mlir.global"`, in generic-form MLIR; a region that builds a constant folds to it,
`X.lit`. `noncomputable mlir_const_def` lets a table too long for the code generator be
noncomputable; or raise `maxRecDepth` to compile it. -/
syntax (name := mlirConstDef) (docComment)? ("noncomputable ")? "mlir_const_def " ident " := "
  mlir_region : command

@[inherit_doc mlirConstDef] syntax (name := mlirConstDefGlobal) (docComment)? ("noncomputable ")?
  "mlir_const_def " ident " := " mlir_symbol : command

elab_rules : command
  |
  `(
$[$doc?:docComment]? $[noncomputable%$nc]? mlir_const_def $x:ident := $r:mlir_region) =>
    do
    elabMlirConstDef doc? nc.isSome x r (← liftCoreM (region r))
  |
  `(
$[$doc?:docComment]? $[noncomputable%$nc]? mlir_const_def $x:ident := $g:mlir_symbol) =>
    do
    elabMlirConstDef doc? nc.isSome x g (← globalRegion g)

/-- `mlir_region% { region }` is the region's AST, a `MLIR.Region`: `translate`'s input. -/
elab "mlir_region% " r:mlir_region : term => do
  return toExpr (← MLIR.region r)

end MLIR

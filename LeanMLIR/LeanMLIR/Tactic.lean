/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework
import LeanMLIR.Util
import LeanMLIR.Tactic.SimpSet

import Qq
import Mathlib.Tactic.FinCases
import Lean.Meta.KAbstract
import Lean.Elab.Tactic.ElabTerm

variable [DialectSignature d] [TyDenote d.Ty] [DialectDenote d] [Monad d.m] [LawfulMonad d.m] in
@[simp_denote]
theorem Expr.denote_unfold' {ty} (e : Expr d Γ eff ty) :
    e.denote V = do
      let x ← e.denoteOp V
      return x ++ V := by
  rw [Expr.denote_unfold, ← map_eq_pure_bind]

namespace SSA

open LeanMLIR
open Ctxt (Var Valuation DerivedCtxt Hom)
open Lean Elab Tactic Meta

attribute [simp_denote] Int.ofNat_eq_coe DerivedCtxt.cons DerivedCtxt.ofCtxt
  DerivedCtxt.ofCtxt_empty Valuation.cons_last Var.zero_eq_last Var.succ_eq_toCons Ctxt.empty
  Ctxt.empty_eq Ctxt.cons Ctxt.Valuation.nil Ctxt.Valuation.cons_last Ctxt.map
  Ctxt.Valuation.cons_eval Ctxt.Valuation.cons_toCons HVector.map HVector.getN HVector.get
  HVector.toSingle HVector.toPair HVector.toTuple DialectDenote.denote Expr.op_mk Expr.args_mk
  DialectMorphism.mapOp DialectMorphism.mapTy List.map Ctxt.cons List.map Function.comp
  Valuation.ofPair Valuation.ofHVector Function.uncurry List.length_singleton Fin.zero_eta
  List.map_eq_map List.map_cons List.map_nil bind_assoc pairBind
  /- `castPureToEff` -/
  Com.letPure Expr.denote_castPureToEff Expr.denote_castPureToEff
  /- Unfold denotation -/
  Com.ret Com.denote_var Com.denote_rets Expr.denoteOp Regions.denote Expr.op_mk Expr.args_mk
  Expr.regArgs_mk Expr.op_castPureToEff Expr.args_castPureToEff
  /- `toPure`: a pure operation sitting in an impure `Com`, as every
     instruction of a region that ends in a store does -/
  Expr.op_toPure Expr.args_toPure Expr.regArgs_toPure
  /- Effect massaging -/
  EffectKind.liftEffect_rfl Id.pure_eq' Id.bind_eq' id_eq pure_bind cast_eq
  -- Valuation append & accesses
  Valuation.nil_append Valuation.cons_append Valuation.cons_last Valuation.cons_toCons
  Valuation.instAppendHVector Valuation.ofHVector_nil Valuation.ofHVector_cons
  /- Misc-/
  and_true true_and implies_true

/-!
NOTE (Here Be Dragons 🐉):
`HVector.denote` has a typeclass assumption `TyDenote (Dialect.Ty d)`, where `d : Dialect`.
However, we tend to define `d` as an `abbrev`, so that our goal statement might have
`HVector.denote` where the concrete instance is `instTyDenote : TyDenote Ty`,
  and `Ty` is the expression that `d` was defined with.

We've observed `simp [HVector.denote]` not working in such situations.
  Even more surprising, `rw [HVector.denote]` *did* succeed in rewriting.
According to Zulip (https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/simp.20.5BX.5D.20fails.2C.20rw.20.5BX.5D.20works/near/358861409):
> simp [(X)] is a standard trick to fix simp [X] not working

By default, it seems that `simp` will synthesize typeclass arguments of a lemma, and then
use the *default* instance to determine whether a simp-lemma applies to the current goal.
Writing `simp [(X)]`, on the other hand, is equivalent to writing `simp [@X _ _ _]`
  (for as many underscores as `X` takes arguments, implicit or explicit).
The parentheses seems to enable `simp` to unify typeclass arguments as well, and thus the
  simp-lemma applies even for non-standard instances.

We've replicated this effect by defining `HVector.denote_{nil,cons}'`, as analogues
to their non-primed lemmas, which instead take all instances as regular implicit
arguments, thus guiding `simp` to unify against non-standard instances.
-/

section

variable {d : Dialect} {instSig : DialectSignature d} {instTyDenote : TyDenote d.Ty}
  {instDenote : DialectDenote d} {instMonad : Monad d.m}

@[simp_denote]
theorem Regions.denote_nil' {eff : EffectKind} (T : Regions d eff []) :
    Regions.denote T = HVector.nil := by
  cases T; simp [Regions.denote]

@[simp_denote]
theorem Regions.denote_cons' {eff : EffectKind} (t : Ctxt d.Ty × List d.Ty)
    (ts : List (Ctxt d.Ty × List d.Ty)) (a : Com d t.1 eff t.2) (as : Regions d eff ts) :
    Regions.denote (.cons a as) = .cons (a.denote) (as.denote) := by simp [Regions.denote]

end

/--
`elimValuation` simplifies universal quantifiers `∀ (V : Valuation [t₁, ..., tₙ])`,
where the context of the valuation is a concrete list of types, into a sequence
of quantifiers `∀ (x0 : ⟦t₁⟧) (x1 : ⟦t₂⟧) ... (xn : ⟦tₙ⟧)`.
-/
simproc [simp_denote]elimValuation (∀ (_ : Ctxt.Valuation _), _) := fun e => do
  let .forallE _name VTy@(mkApp3 (.const ``Ctxt.Valuation _) Ty instTyDenote Γ) body _info := e
    | return .continue
  let Γlist ← mkFreshExprMVar none
  unless ← isDefEq Γ (mkApp2 (mkConst ``Ctxt.ofList) Ty Γlist) do
    return .continue
  let some (_, Γelems) := (← instantiateMVars Γlist).listLit?
    | return .continue
  let Γelems := Γelems.toArray.reverse
  let xsTypes := Γelems.map (mkApp3 (mkConst ``TyDenote.toType) Ty instTyDenote)
  let declInfo :=
    xsTypes.mapIdx fun i ty =>
      let x := if i == 0 then "e" else s!"e_{i}"
      (Name.mkSimple x, ty)
  withLocalDeclsDND declInfo <| fun xs => do
      let V := Valuation.mkOfElems Ty instTyDenote Γelems xs
      let newType ← mkForallFVars xs (body.instantiate1 V)
      let proof :=
        let mp :=
          ←
            withLocalDeclD .anonymous e <| fun eProof => do
                mkLambdaFVars (#[eProof] ++ xs) <| mkApp eProof V
        let mpr :=
          ←
            withLocalDeclD .anonymous newType <| fun newProof =>
                withLocalDeclD .anonymous VTy <| fun V => do
                  let xs ←
                    Γelems.reverse.mapIdxM fun i ty =>
                        let v := Ctxt.mkVar Ty Γ ty (toExpr i) none
                        pure <| mkApp2 V ty v
                  mkLambdaFVars #[newProof, V] <| mkAppN newProof xs.reverse
        mkApp3 (mkConst ``propext) e newType <| mkApp4 (mkConst ``Iff.intro) e newType mp mpr
      return .visit { expr := newType, proof? := some proof }

section SimpValuationApply

/-- Split a valuation into the statically known elements at its *end* and the rest.
That is, `V ::ₕ x ::ₕ y` with `V` a free variable gives `(#[y, x], V)`. -/
private partial def valuationElements (e : Expr) (elems : Array Expr := #[]) : Array Expr × Expr :=
  match_expr e with
  | Valuation.cons _Ty _instTyDenote _Γ _t x V => valuationElements V (elems.push x)
  | _ => (elems, e)

private partial def varToIndex (e : Expr) : Option Nat :=
  match_expr e with
  | Var.mk _Ty _Γ _t i _hi => Expr.numeral? i
  | Subtype.mk _α _p i _hi => Expr.numeral? i
  | Var.last _Ty _Γ _t => some 0
  | Var.toCons _Ty _Γ _t _t' v => (· + 1) <$> varToIndex v
  | _ => none

/--
`simpValuationApply` rewrites a valuation applied to a *fully-concrete* variable
to the element, or, past the statically known elements, to the rest of the
valuation at the shifted variable. It runs before rewrite lemmas (`↓`):
`Valuation.cons_eval` matches the same terms and walks one `cons` per rewrite.
-/
dsimproc ↓[simp_denote]simpValuationApply ((Valuation.cons _ _) _) := fun e => do
  let mkApp2 V t v := e
    | return .continue
  withTraceNode `LeanMLIR.Elab (fun _ => pure m!"Simplifying access of variable: …") <| do
      trace[LeanMLIR.Elab] "Valuation: {V}"
      trace[LeanMLIR.ELab] "Variable: {v}"
      let (Velems, Vrest) := valuationElements V
      let some i := varToIndex v
        |
        trace[LeanMLIR.Elab] "{Lean.crossEmoji} Expected a fully concrete variable, but found: {v}"
        return .continue
      if let some x := Velems[i]? then
        return .visit x
      -- `⟨i - Velems.size, h⟩` into `Vrest`; `h` has that type up to defeq
      let_expr Subtype.mk _α _p _i h := v
        | return .continue
      let .forallE _ _ body _ ← whnfD (← inferType Vrest) | return .continue
      let varTy ← whnfD (body.instantiate1 t).bindingDomain!
      let_expr Subtype α p := varTy
        | return .continue
      let v' :=
        mkApp4 (.const ``Subtype.mk varTy.getAppFn.constLevels!) α p (mkNatLit (i - Velems.size)) h
      return .visit (mkApp2 Vrest t v')

end SimpValuationApply

/-! ### HVector rewrites -/

/-! #### HVector.get -/

section SimpHVectorGet

/--
Return `some i` if `e` is one of the following

- `Fin.mk e _`, where `isNumeral e`
- `Fin.succ j`, where `j` is a `finNumeral`
- `OfNat.ofNat e`, where `isNumeral e`
-/
partial def finNumeral? (e : Lean.Expr) : Option Nat :=
  match_expr e with
  | Fin.mk _ i _h => Expr.numeral? i
  | Fin.succ _ i => (· + 1) <$> finNumeral? i
  | OfNat.ofNat α i _ => do
    let_expr Fin n := α | none
    let n ← Expr.numeral? n
    let i ← Expr.numeral? i
    some (i % n)
  | _ => none

dsimproc simpHVectorGet (HVector.get _ _) := fun e => do
  let_expr HVector.get _α _A _as xs i := e
    | return .continue
  withTraceNode `LeanMLIR.Elab (fun _ => pure m!"Simplifying: {e}") <| do
      let some i := finNumeral? i
        |
        trace[LeanMLIR.Elab] "Unable to statically determine the value of `Fin` expression: {i}"
        return .continue
      let rec getElem (xs : Expr) (i : Nat) : MetaM (Option Expr) := do
        let_expr HVector.cons _α _f _as _a x xs := xs
          |
          trace[LeanMLIR.Elab] "Expected an application of `HVector.cons`, but found: {xs}"
          return none
        match i with
        | 0 =>
          return some x
        | i + 1 =>
          getElem xs i
      let some x ← getElem xs i | return .continue
      return .visit x

end SimpHVectorGet

/-!
#### HVector.cons injectivity

WORKAROUND: Simplifying the semantics can yield equalities of the form:
  `@Eq (Id <| HVector _ _) (x ::ₕ xs) (y ::ₕ ys)`
The `Id _` in the type of the equality somehow blocks the injectivity theorem
for `HVector.cons` from applying, so we first have to clean up the equality.
-/

@[simp_denote]
theorem eq_id_iff (x y : α) : @Eq (Id α) x y ↔ x = y := by rfl

@[simp_denote]
theorem HVector.cons_inj {α : Type u_1} {f : α → Type u_2} {as : List α} {a : α} (x y : f a)
    (xs ys : HVector f as) : @Eq (no_index _) (x::ₕxs) (y::ₕys) ↔ (x = y ∧ xs = ys) := by
  rw [HVector.cons.injEq]

/-!
#### Miscellaneous HVector Rewrites
-/

attribute [simp_denote] HVector.map'_cons HVector.map'_nil

/-! ### Compatibility Wrappers -/

attribute [simp_denote] SingleReturnCompat.Com SingleReturnCompat.Expr SingleReturnCompat.Com.var

/-!
## Simp_peephole
-/

open Lean.Parser.Tactic (location)

/--
`simp_peephole` simplifies away the framework overhead of denoting expressions/programs.

NOTE: crucial rewrites (in particular, `Com.denote_var`) will only apply if the
dialect monad `d.m` is known to be lawful. If `simp_peephole` is not simplifying
as expected, first verify that a `LawfulMonad d.m` instance is synthesizable.
-/
macro "simp_peephole" loc:(location)? : tactic =>
  `(tactic|(
      -- First, we ensure potential quantification over a Valuation is made explicit
      first
      | rw [funext_iff (α := Ctxt.Valuation _)] $[$loc]?
      | change ∀ (_ : Ctxt.Valuation _), _ $[$loc]?
      | skip

      -- Then, we simplify with the `simp_denote` simpset
      simp (config := {failIfUnchanged := false}) only
        [Expr.denote_castPureToEff, simp_denote] $[$loc]?
      -- ^^^^^^^^^^^^^^^^^^^^^^^^^
      -- `denote_castPureToEff` is already part of the simp_denote simpset
      -- Still, omitting it here somehow causes motive-related errors.
  ))

/-
TODO: Implement a check for `LawfulMonad`.
If a dialect's monad doesn't implement LawfulMonad, then currently `simp_peephole`
just silently fails to apply `Com.denote_var`, leaving the goal state messy
without any indication on what's wrong. We should catch this, and show a failed
to synthesize error.
-/

end SSA

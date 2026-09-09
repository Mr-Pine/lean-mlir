/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.MLIR.DenoteStep

/-!
# Sealing a block's valuation

A block walk carries its valuation as a `cons` spine, one entry per
instruction stepped. Every tactic in the walk -- `simp_peephole` under
`denote_eval`, the `simp_spine` pass in each `peel_*` -- traverses that spine,
so a block of `n` instructions costs `Θ(n²)` however carefully each step is
written (`LIMITATIONS.md` 9).

`denote_seal` cuts that. It replaces the spine with a fresh opaque variable
and keeps exactly the facts the rest of the block reads, so the walk restarts
from a valuation of size one. Nothing about the *program* is named -- the
residual `BlockCom` stays in the goal as it was -- which is what makes this
work where naming the suffix (`BlockCom.drop`) does not: there is no
`residual =?= drop n body` for the elaborator to reduce.

    denote_seal W with x235 := hv235, c17 := env.c17

leaves `W` in place of the spine, `x235 : W ⟨23, _⟩ = …` and
`c17 : W ⟨237, _⟩ = …`. Both indices are found by the tactic: a hypothesis
whose left-hand side is a value the walk pushed is located in the spine, and
one that reads the ambient valuation (`env`'s fields, `V ⟨181⟩ = …`) is
shifted by the spine's height. An item that is not an equation is a value the
walk substituted rather than named -- a call's return, say -- and stands for
itself.
-/

namespace Firedancer
open Lean Meta Elab Tactic
open LeanMLIR SLLVM

/-- The spine taken apart: `(type, value)` of each `cons`, outermost first,
and the base it sits on. -/
private partial def spineElems (S : Expr) : Array (Expr × Expr) × Expr :=
  go S #[]
where
  go (e : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) × Expr :=
    if e.isAppOfArity ``Ctxt.Valuation.cons 6 then
      let as := e.getAppArgs
      go as[5]! (acc.push (as[3]!, as[4]!))
    else (acc, e)

/-- The index a kept fact reads, and the type it reads at: a value the walk
pushed is in the spine, a read of the ambient valuation (`V ⟨k, _⟩`) is the
same variable `elems.size` further in, and anything else is looked for in the
base -- the block's own arguments, which `ofHVector` holds rather than
`cons`. -/
private def keptIndex (Γ S : Expr) (elems : Array (Expr × Expr)) (lhs : Expr) :
    MetaM (Nat × Expr) := do
  if let some j := elems.findIdx? (fun (_, v) => v == lhs) then
    return (j, elems[j]!.1)
  if lhs.getAppNumArgs == 2 then
    let ty := lhs.getAppArgs[0]!
    let v := lhs.getAppArgs[1]!
    -- `⟨i, _⟩` is `Subtype.mk` or `Ctxt.Var.mk` depending on how it was
    -- written; take the first literal argument either way
    if let some k := v.getAppArgs.findSome? (·.nat?) then
      return (elems.size + k, ty)
  -- the base: probe the first few positions past the spine, reading each
  -- position's type out of the context rather than guessing it
  for k in [0:32] do
    let i := elems.size + k
    let some ty ← (do
        let o ← whnf (← mkAppM ``getElem? #[Γ, mkNatLit i])
        pure (if o.isAppOfArity ``Option.some 2 then some o.appArg! else none))
      | continue
    let some val ← (try
        let v ← mkAppOptM ``Ctxt.Var.mk #[none, some Γ, some ty, some (mkNatLit i),
          some (← mkEqRefl (← mkAppOptM ``Option.some #[none, some ty]))]
        pure (some (← whnf (mkApp2 S ty v)))
      catch _ => pure none)
      | continue
    if ← isDefEq val lhs then return (i, ty)
  throwError "denote_seal: {lhs} is neither a stepped value, an ambient read, nor in the base"

syntax sealItem := ident " := " term

open Lean.Parser.Tactic in
/-- `denote_seal W with n₁ := h₁, …` -- replace the walk's valuation with a
fresh `W`, keeping `h₁ …` as facts about it under the names `n₁ …`. -/
elab "denote_seal " w:ident " with " items:sealItem,* : tactic => do
  let goal ← getMainGoal
  let goal' ← goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    let some dapp := tgt.find? (fun e =>
        e.isAppOfArity ``BlockCom.denote 6 && e.appArg!.isAppOfArity ``Ctxt.Valuation.cons 6)
      | throwError "denote_seal: the goal has no block denotation over a `cons` valuation"
    let Γ := dapp.getAppArgs[0]!
    let S := dapp.appArg!
    let (elems, _) := spineElems S
    let mut facts : Array (Name × Expr × Expr) := #[]
    for it in items.getElems do
      let nm := it.raw[0].getId
      let hE ← elabTerm (⟨it.raw[2]⟩ : Term) none
      let hTy ← instantiateMVars (← inferType hE)
      -- an equation names the value and what it is; a bare term names a value
      -- the walk substituted rather than named, and stands for itself
      let (lhs, rhs, prf) := match hTy.eq? with
        | some (_, l, r) => (l, r, hE)
        | none => (hE, hE, hE)
      let prf ← if hTy.eq?.isSome then pure prf else mkEqRefl prf
      let (i, ty) ← keptIndex Γ S elems lhs
      -- elaborated from syntax rather than assembled: the index proof has to
      -- be the one `by rfl` builds against the stated type, and the variable
      -- the `⟨i, _⟩` a stepped goal writes, or `simp` will not match it
      let Γstx ← Term.exprToSyntax Γ
      let tystx ← Term.exprToSyntax ty
      let v ← Term.elabTerm
        (← `((⟨$(Syntax.mkNumLit (toString i)), by rfl⟩ : Ctxt.Var $Γstx $tystx))) none
      Term.synthesizeSyntheticMVarsNoPostponing
      facts := facts.push (nm, ← mkEq (mkApp2 S ty v) rhs, prf)
    let mut g := goal
    for (nm, ty, prf) in facts do
      g ← g.assert nm ty prf
    let (_, g₁) ← g.generalize #[{ expr := S, xName? := w.getId }]
    let (_, g₂) ← g₁.introNP facts.size
    return g₂
  replaceMainGoal [goal']

end Firedancer

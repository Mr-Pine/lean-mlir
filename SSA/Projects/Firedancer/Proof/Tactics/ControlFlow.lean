import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Avx512.Spec.Quad

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Firedancer.Avx512 (vecBV flatten_vecBV)

-- v4.34: `BlockCom.call` indexes the callee's entry block by `Ctxt.ofList argTys.reverse`,
-- so a call node is only type-correct up to `List.reverse` of a literal list. Applications
-- are now checked at `implicit` transparency, where a core `def` does not unfold, and every
-- `rw` through a call node fails. `List.reverse` cannot be marked from outside its own file
-- without this override.
set_option allowUnsafeReducibility true in
attribute [implicit_reducible] List.reverse List.reverseAux

open Lean Meta Elab Tactic in
/-- Is `h`'s valuation written `Ctxt.Valuation.ofHVector`?

That is exactly the condition for the by-reference step lemmas. They take
`argVals` as a variable of their own and pick it up from `h` by first-order
matching against `Ctxt.Valuation.ofHVector argVals`; the operands are then tied
back to the goal by `hargs`, a side goal the caller can aim tactics at. A spec
that phrases its valuation some other way -- `Ctxt.Valuation.singleton` for a
one-argument callee, or a named valuation like `quadDualValuation` -- is defeq
but not syntactically that, so the match fails and there is nothing to assign.

Those `h` have to go through the general lemma, whose `argVals` *is* the goal's
own operand expression and which therefore needs no matching at all. Getting it
backwards is not a failure but a whole-program defeq: the tactic spends the
heartbeat budget rather than falling over. Hence the dispatch, rather than a
`first` over both. -/
def callArgsAreOfHVector (h : Term) : TacticM Bool :=
  withMainContext do
    withoutModifyingState do
      let ty ← instantiateMVars (← inferType (← Term.elabTerm h none))
      return (ty.find? (·.isAppOf ``Ctxt.Valuation.ofHVector)).isSome

open Lean Meta Elab Tactic in
/-- The body of `peel_call`. `extra` are extra lemmas for
the side goal that evaluates the call's *operands*; the three lemma names
select the value-returning or the void family of step lemmas.

There is no alternative for a callee whose program is *inlined* into the
caller -- a `sllvm_cfg_of` binding `@f := f_region` rather than a `Cfg`
constant. Nothing in the tree peels one: the four regions that inline a callee
are derived through `run_denote_var_zero` and the low-level step lemmas
instead. `run_denote_call_of_nil`/`_of_value` remain, unused by this tactic,
for whenever one does.

`argTys` is read off the goal's `BlockCom.call` node and pinned: `argVals`
has type `HVector toType argTys.reverse`, so leaving it open asks Lean to
invert `List.reverse` on an unknown list -- which does not fail, it grinds
until the heartbeat limit. -/
def peelCallCore (cfgLemN bindCfgLemN bindLemN : Name) (h : Term)
    (extra : Array Term) : TacticM Unit := do
  -- `call {Γ Γout rets succs argTys retTys csigs cΓout} callee centry cblocks args body`
  let (argTys, isBind) ← (← getMainGoal).withContext do
    let tgt ← instantiateMVars (← (← getMainGoal).getType)
    let some callApp := tgt.find? (·.isAppOf ``LeanMLIR.SLLVM.BlockCom.call)
      | throwError "peel_call: no `BlockCom.call` in the goal"
    let as := callApp.getAppArgs
    unless as.size ≥ 5 do throwError "peel_call: malformed `BlockCom.call`"
    -- Bind or bare: is the call's *denotation* the argument of a `bind`? An
    -- entry block's always is -- `Cfg.denote` runs it and then `match`es on how
    -- it ended, and that `match` is the continuation. A tail block reached
    -- through `Blocks.run_loop` is stated one block at a time, so there is
    -- nothing after it. Unlike by-reference-vs-general, this one is a fact
    -- about the goal rather than a preference, so it is read rather than tried.
    --
    -- Asked directly -- is some `bind` applied to a call's denotation -- rather
    -- than by finding one denotation and looking for it as a `bind` argument.
    -- The latter compares two `Expr`s with `==`, which a walk far enough into a
    -- region gets wrong: the residual program holds the *later* calls too, so
    -- the denotation `find?` returns need not be the one the head `bind` holds,
    -- and the check then reads `false` on a block whose call is plainly bound.
    let isDenoteCall (e : Expr) : Bool :=
      e.isAppOf ``LeanMLIR.SLLVM.BlockCom.denote
        && e.getAppArgs.any (·.isAppOf ``LeanMLIR.SLLVM.BlockCom.call)
    let isBind := (tgt.find? fun e =>
      e.isAppOf ``Bind.bind && e.getAppArgs.any (fun a => isDenoteCall a.consumeMData)).isSome
    pure (as[4]!, isBind)
  -- all four `reverse`/`reverseAux` equations: with an opaque valuation the
  -- operand list is `(map V args).reverse`, and it only closes if the whole
  -- `reverseAux` recursion unfolds
  let defaults : Array Term ← #[
      ← `(HVector.map), ← `(HVector.reverse_nil), ← `(HVector.reverse_cons),
      ← `(HVector.reverseAux_nil), ← `(HVector.reverseAux_cons),
      ← `(Ctxt.Valuation.ofHVector_nil), ← `(Ctxt.Valuation.ofHVector_cons),
      ← `(Ctxt.Valuation.nil_append), ← `(Ctxt.Valuation.cons_append),
      ← `(Ctxt.Valuation.cons_succ)].mapM pure
  let simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    (defaults ++ extra).mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let tys ← argTys.toSyntax
  let cfgLem     := mkIdent cfgLemN
  let bindCfgLem := mkIdent bindCfgLemN
  let bindLem    := mkIdent bindLemN
  -- The `>>=` shape with the operand vector *supplied*, tried only when there
  -- are `with` lemmas -- that is, only in a tail block, where the ambient
  -- valuation is opaque and `(args.map V).reverse` is not defeq to the
  -- callee's argument list until those lemmas have rewritten each lookup. The
  -- plain bind lemma has no `hargs`, so there its `exact` grinds on a defeq
  -- check it cannot discharge rather than failing over. With a *concrete*
  -- valuation the plain path already works, and taking this one instead
  -- changes which `argVals` gets picked -- hence the gate.
  -- v4.34: the `bind` around the call carries the lifted `Cfg`'s `Γout`/`sigs`; reduce them
  -- or the target is not type-correct at `implicit` transparency and no `rw` matches.
  evalTactic (← `(tactic| reduce_cfg_indices))
  let byRef ← callArgsAreOfHVector h
  unless !byRef || !isBind do
    if ← (do evalTactic (← `(tactic| rw [$bindCfgLem:ident (argTys := $tys)
        (by first | (simp only [$[$simpArgs],*]; done) | rfl) $h])); pure true) <|> pure false then
      return
  -- ... and, if that read of the goal was wrong, the other one: both by-reference
  -- lemmas are tried before the general path, whose `hargs`-free `exact` needs
  -- the operands to be *defeq* to the callee's argument list -- which at a call
  -- site whose operands are hypotheses rather than substituted values they are
  -- not, so the caller would have to `subst` them into the residual program.
  unless !byRef || !isBind do
    if ← (do evalTactic (← `(tactic| rw [$cfgLem:ident (argTys := $tys)
        (by first | (simp only [$[$simpArgs],*]; done) | rfl) $h])); pure true) <|> pure false then
      return
  -- ... and the same for a *bare* block, where the call is the block's own
  -- denotation rather than a `>>=`. Without this the `first` below reaches
  -- `cfgLem`, whose `hargs` is a full `simp` over the local context: on a
  -- `fd_r43x6` loop body that runs for 27s and then fails on the step limit,
  -- all before the alternative that does work is tried. The `simp only` here
  -- discharges the same goal instantly.
  unless !byRef || isBind do
    if ← (do evalTactic (← `(tactic| rw [$cfgLem:ident (argTys := $tys)
        (by first | (simp only [$[$simpArgs],*]; done) | rfl) $h])); pure true) <|> pure false then
      return
  -- No `hargs` on this one: the operand vector is whatever unifying with `h`
  -- picks. Its two branches reconcile `h`'s callee with the one the node holds
  -- -- `Cfg.ofCom` of a `Com` constant, or a `Cfg` constant. There is
  -- deliberately no bare `exact $h` third branch: this pattern matches *any*
  -- call node, so an `h` about a different callee would reach that `exact` and
  -- be left deciding a defeq between two whole programs, spending the
  -- heartbeat budget rather than failing over. Failing here is what makes a
  -- mismatched `h` a fast, legible error.
  evalTactic (← `(tactic| first
    -- the `>>=` shape `Cfg.denote` produces: the common case
    | rw [$bindLem:ident (argTys := $tys)
        (by first
          | (rw [Cfg.denote_mk_ofCom]; exact $h)
          | (rw [Cfg.denote_mk_self]; exact $h))]
    -- a bare block denotation (a `Blocks.run_loop` step), callee by reference
    | rw [$cfgLem:ident (argTys := $tys)
        (by simp [$[$simpArgs],*, *])
        $h]))

open Lean Meta Elab Tactic in
/-- Does the callee return a value? Read off `h`'s right-hand side, which every
conformance theorem states as `.value (rets, t')`: `rets` is `[x]ₕ` for a
value-returning callee and `.nil` for an out-parameter one. Elaborating `h`
here is only to classify it; the emitted tactic elaborates it again for real,
as `peel_store` does with its stored value.

This is what lets one `peel_call` cover both families: the choice was never a
judgement call, it is written in the lemma the caller already has. -/
def callReturnsValue (h : Term) : TacticM Bool :=
  withMainContext do
    let ty ← withoutModifyingState do
      whnf (← instantiateMVars (← inferType (← Term.elabTerm h none)))
    let some (_, _, rhs) := ty.eq?
      | throwError "peel_call: {← ppExpr ty} is not a run equation"
    -- `.value (rets, t')` -- the `rets` is the first component of the pair
    let rets ← withoutModifyingState do
      let some pair := rhs.getAppArgs.back? | throwError "peel_call: no `.value` payload"
      whnf (← instantiateMVars (pair.getAppArgs[2]?.getD pair))
    return !rets.isAppOf ``HVector.nil

open Lean Elab Tactic in
/-- The three step-lemma names for the value- or the nil-returning family. -/
def peelCallNames (value : Bool) : Name × Name × Name :=
  if value then
    (``LeanMLIR.SLLVM.BlockCom.run_denote_call_cfg_of_value,
     ``LeanMLIR.SLLVM.BlockCom.run_bind_denote_call_cfg_of_value,
     ``LeanMLIR.SLLVM.BlockCom.run_bind_denote_call_of_value)
  else
    (``LeanMLIR.SLLVM.BlockCom.run_denote_call_cfg_of_nil,
     ``LeanMLIR.SLLVM.BlockCom.run_bind_denote_call_cfg_of_nil,
     ``LeanMLIR.SLLVM.BlockCom.run_bind_denote_call_of_nil)

open Lean Elab Tactic in
/-- `peel_call h` runs the next call, given the callee's run equation `h` --
the form its conformance theorem is stated in.

Everything the tactic can work out, it works out. Whether the callee returns a
value or nothing is read off `h`'s right-hand side by `callReturnsValue`;
whether the call sits under a `>>=` is read off the goal by `peelCallCore`.
Neither was ever a judgement call -- one is written in the lemma the caller
already has, the other in the block they are standing in.

What is left is the one choice no one can read: whether to take the
by-reference lemma, whose `argVals` is its own variable tied to the goal by
`hargs`, or the general one, whose `argVals` *is* the goal's operand
expression. Both apply almost everywhere and they leave differently-shaped
goals, so it stays with the caller -- see the `with` form. -/
elab "peel_call " h:term : tactic => do
  let (a, b, c) := peelCallNames (← callReturnsValue h)
  peelCallCore a b c h #[]

open Lean Elab Tactic in
/-- `peel_call h with l₁, l₂` takes the by-reference lemma, with `l₁, l₂` as
extra lemmas for `hargs` -- the side goal that says what the call's operands
are.

Reach for it when `h`'s operands are concrete and the block's are not
syntactically the same, which is the case whenever the ambient valuation is
opaque (a tail block reading past its own arguments) or simply long. Left to
the general lemma those two have to be reconciled inside an `exact`, and that
is a whole-program defeq: it does not fail, it spends the heartbeat budget.

`hargs` is tried by `simp only` and then `rfl`, so the list is often empty of
anything load-bearing -- but passing it is what selects this path. -/
elab "peel_call " h:term " with " l:term,+ : tactic => do
  let (a, b, c) := peelCallNames (← callReturnsValue h)
  peelCallCore a b c h l.getElems

macro "simp_return" : tactic =>
  -- v4.34: `simp` stops at the terminator's `pure`-bind, whose `.2` no longer reduces.
  `(tactic| simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm,
      Ctxt.Valuation.singleton] <;> rfl)

end Firedancer

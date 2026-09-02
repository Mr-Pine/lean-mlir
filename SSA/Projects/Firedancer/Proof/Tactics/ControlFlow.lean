import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Avx512.Spec.Quad

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Firedancer.Avx512 (vecBV flatten_vecBV)

open Lean Meta Elab Tactic in
/-- The body of `peel_call`. `extra` are extra lemmas for the side goal that
evaluates the call's *operands*.

`argTys` is read off the goal's `BlockCom.call` node and pinned: `argVals`
has type `HVector toType argTys.reverse`, so leaving it open asks Lean to
invert `List.reverse` on an unknown list -- which does not fail, it grinds
until the heartbeat limit. -/
def peelCallCore (h : Term) (extra : Array Term) : TacticM Unit := do
  -- `call {Γ Γout rets succs argTys retTys csigs cΓout} callee centry cblocks args body`
  let argTys ← (← getMainGoal).withContext do
    let tgt ← instantiateMVars (← (← getMainGoal).getType)
    let some callApp := tgt.find? (·.isAppOf ``LeanMLIR.SLLVM.BlockCom.call)
      | throwError "peel_call: no `BlockCom.call` in the goal"
    let as := callApp.getAppArgs
    unless as.size ≥ 5 do throwError "peel_call: malformed `BlockCom.call`"
    pure as[4]!
  let defaults : Array Term ← #[
      ← `(HVector.map), ← `(HVector.reverse_cons), ← `(HVector.reverseAux_nil),
      ← `(Ctxt.Valuation.ofHVector_nil), ← `(Ctxt.Valuation.ofHVector_cons),
      ← `(Ctxt.Valuation.nil_append), ← `(Ctxt.Valuation.cons_append),
      ← `(Ctxt.Valuation.cons_succ)].mapM pure
  let simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    (defaults ++ extra).mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let tys ← argTys.toSyntax
  let cfgLem  := mkIdent ``LeanMLIR.SLLVM.BlockCom.run_denote_call_cfg_of_value
  let bindLem := mkIdent ``LeanMLIR.SLLVM.BlockCom.run_bind_denote_call_of_value
  let bareLem := mkIdent ``LeanMLIR.SLLVM.BlockCom.run_denote_call_of_value
  evalTactic (← `(tactic| first
    -- the `>>=` shape `Cfg.denote` produces: the common case
    | rw [$bindLem:ident (argTys := $tys)
        (by first
          | (rw [Cfg.denote_mk_ofCom]; exact $h)
          | (rw [Cfg.denote_mk_self]; exact $h)
          | exact $h)]
    -- a bare block denotation (a `Blocks.run_loop` step), callee by reference
    | rw [$cfgLem:ident (argTys := $tys)
        (by simp [$[$simpArgs],*, *])
        $h]
    -- bare, with the callee inlined rather than by reference
    | rw [$bareLem:ident (argTys := $tys)
        (by first
          | (rw [Cfg.denote_mk_ofCom]; exact $h)
          | (rw [Cfg.denote_mk_self]; exact $h)
          | exact $h)]))

open Lean Elab Tactic in
/-- `peel_call h` runs the next call that returns a value, given the callee's
run equation `h` -- the form its conformance theorem is stated in. A callee
embedded by reference (`Cfg.ofCom` of a `Com` constant, or a `Cfg` constant)
is folded back to that constant's own `denote`.

`h : StateT.run (runFunction (callee.denote V)) t = .value ([x]ₕ, t')` -/
elab "peel_call " h:term : tactic => peelCallCore h #[]

open Lean Elab Tactic in
/-- `peel_call h with l₁, l₂` is `peel_call h` with extra lemmas for the goal
that evaluates the call's operands. That goal is trivial when the block's
valuation is concrete (`Cfg.denote` proofs), but a loop body reads its
ambient values through an opaque valuation, so there the operands are only
known from `EntryEnv`-style facts -- pass them here, or destructure the
structure beforehand and let the `simp [*]` find them. -/
elab "peel_call " h:term " with " l:term,+ : tactic => peelCallCore h l.getElems

macro "simp_return" : tactic =>
  `(tactic| simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm, Ctxt.Valuation.singleton])

end Firedancer

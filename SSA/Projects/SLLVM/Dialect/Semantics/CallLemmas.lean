/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect.Basic

/-!
# Reasoning about `llvm.call`

`Com` has no symbol table, so a call carries its callee as a region. The one
lemma worth stating about that is the obvious one: a call denotes to its
callee's denotation, applied to the call's arguments.

It is what makes a proof about a callee *reusable*. Without it, a caller's
derivation would step through the callee's instructions again at every call
site; with it, the call is a single rewrite to whatever the callee was already
shown to compute.
-/

namespace LeanMLIR.SLLVM

open LeanMLIR

-- v4.34: `SLLVM` is semireducible, so `SLLVM.Op`/`SLLVM.m` no longer reduce when applications
-- are type-checked at `implicit` transparency and `Expr.op_mk` cannot fire under `denoteOp`.
-- TODO: belongs unscoped on the `def` in `SSA/Projects/SLLVM/Dialect/Basic.lean`.

/-- **Denotation of a pure call**: the callee's denotation applied to the
call's arguments. Note the `reverse`: block arguments enter a `Ctxt` in
reverse declaration order, so the operand list has to be turned around before
it becomes a valuation of the callee's context. -/
@[simp_denote] theorem denoteOp_call {Γ : Ctxt SLLVM.Ty}
    {callee : String} {argTys retTys : List SLLVM.Ty}
    (args : HVector (Ctxt.Var Γ) argTys)
    (com : Com SLLVM (Ctxt.ofList argTys.reverse) .pure retTys)
    (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
      (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .pure)
        (SLLVMOp.call callee argTys retTys .pure) rfl (EffectKind.le_refl _) args
        (Regions.cons com Regions.nil)) V
      = com.denote (Ctxt.Valuation.ofHVector (args.map V).reverse) := by
  rfl

/-- **Denotation of an impure call**: the callee's denotation applied to the
call's arguments, run as a function (`runFunction`): the callee's frame --
every block allocated during the call, i.e. with id at least the counter's
value at entry -- is dead in the state the call returns and the counter is
restored. A pointer into the frame that escaped the call takes the
freed-already UB path on use, as a real dangling stack pointer would. -/
@[simp_denote] theorem denoteOp_call_impure {Γ : Ctxt SLLVM.Ty}
    {callee : String} {argTys retTys : List SLLVM.Ty}
    (args : HVector (Ctxt.Var Γ) argTys)
    (com : Com SLLVM (Ctxt.ofList argTys.reverse) .impure retTys)
    (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
      (Expr.mk (d := SLLVM) (Γ := Γ) (eff := .impure)
        (SLLVMOp.call callee argTys retTys .impure) rfl (EffectKind.le_refl _) args
        (Regions.cons com Regions.nil)) V
      = runFunction (com.denote (Ctxt.Valuation.ofHVector (args.map V).reverse)) := by
  rfl

end LeanMLIR.SLLVM

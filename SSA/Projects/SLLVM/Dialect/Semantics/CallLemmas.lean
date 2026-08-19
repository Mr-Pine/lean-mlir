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

/-- **Denotation of a call.** Note the `reverse`: block arguments enter a `Ctxt`
in reverse declaration order, so the operand list has to be turned around before
it becomes a valuation of the callee's context. -/
@[simp_denote] theorem denoteOp_call {Γ : Ctxt SLLVM.Ty} {eff : EffectKind}
    {callee : String} {argTys : List SLLVM.Ty} {retTy : SLLVM.Ty}
    (args : HVector (Ctxt.Var Γ) argTys)
    (com : Com SLLVM (Ctxt.ofList argTys.reverse) eff [retTy])
    (V : Ctxt.Valuation Γ) :
    Expr.denoteOp
      (Expr.mk (d := SLLVM) (Γ := Γ) (eff := eff)
        (SLLVMOp.call callee argTys retTy eff) rfl (EffectKind.le_refl _) args
        (Regions.cons com Regions.nil)) V
      = com.denote (Ctxt.Valuation.ofHVector (args.map V).reverse) := by
  cases eff <;>
    simp [Expr.denoteOp, Regions.denote, EffectKind.liftEffect,
      DialectSignature.effectKind, DialectSignature.signature, DialectDenote.denote]

end LeanMLIR.SLLVM

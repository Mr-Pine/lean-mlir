/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofData
namespace AgaveLatticeHash.MLIR.BlockPrefix
open LeanMLIR SLLVM

inductive Same : {Γ Δ : Ctxt SLLVM.Ty} → BlockPrefix Γ Δ → BlockPrefix Γ Δ → Prop
  | nil : Same .nil .nil
  | var {e : Expr SLLVM Γ .impure ts} {p q : BlockPrefix (ts ++ Γ) Δ}
      (h : Same p q) : Same (.var e p) (.var e q)
  | left {e : Expr SLLVM Γ .impure []} {p q : BlockPrefix Γ Δ}
      (he : ∀ V, e.denote V = pure V) (h : Same p q) : Same (.var e p) q
  | right {e : Expr SLLVM Γ .impure []} {p q : BlockPrefix Γ Δ}
      (he : ∀ V, e.denote V = pure V) (h : Same p q) : Same p (.var e q)

theorem Same.denote_eq {p q : BlockPrefix Γ Δ} (h : Same p q) (V : Γ.Valuation) :
    p.denote V = q.denote V := by
  induction h with
  | nil => rfl
  | var h ih =>
    simp only [denote]
    congr 1
    funext W
    exact ih W
  | left he h ih => simp only [denote, he, pure_bind, ih]
  | right he h ih => simp only [denote, he, pure_bind, ih]
end AgaveLatticeHash.MLIR.BlockPrefix

namespace AgaveLatticeHash.MLIR.PortableXof
open LeanMLIR SLLVM
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem inputs_same : BlockPrefix.Same preInput.pre xofInput.pre := by
  repeat first
  | apply BlockPrefix.Same.var
  | apply BlockPrefix.Same.left (by
      intro V
      simp [Expr.denote_unfold, Expr.denoteOp, simp_denote, simp_sllvm] <;>
        exact congrArg pure Ctxt.Valuation.nil_append)
  | apply BlockPrefix.Same.right (by
      intro V
      simp [Expr.denote_unfold, Expr.denoteOp, simp_denote, simp_sllvm] <;>
        exact congrArg pure Ctxt.Valuation.nil_append)
  | exact BlockPrefix.Same.nil

end AgaveLatticeHash.MLIR.PortableXof

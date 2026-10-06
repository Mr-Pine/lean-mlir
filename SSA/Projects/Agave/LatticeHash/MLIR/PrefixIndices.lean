/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PrefixTransport

namespace AgaveLatticeHash.MLIR.BlockPrefix
open LeanMLIR SLLVM

theorem input_length_le (p : BlockPrefix Γ Δ) : Γ.length ≤ Δ.length := by
  induction p with
  | nil => exact Nat.le_refl _
  | var e p ih =>
    simp only [Ctxt.length_append, Ctxt.length_ofList] at ih
    omega

/-- The incoming context shifts by the number of SSA results, independently
of the instruction bodies and memory effects. -/
theorem contextHom_val (p : BlockPrefix Γ Δ) (v : Γ.Var t) :
    (p.contextHom v).val = v.val + (Δ.length - Γ.length) := by
  induction p with
  | nil => simp [contextHom]
  | var e p ih =>
    rw [contextHom, ih]
    have hlen := input_length_le p
    simp only [Expr.contextHom, Ctxt.Hom.appendCodomain_apply, Ctxt.Hom.id,
      Ctxt.Var.val_appendInr]
    simp only [Ctxt.length_append, Ctxt.length_ofList] at hlen ⊢
    omega

end AgaveLatticeHash.MLIR.BlockPrefix

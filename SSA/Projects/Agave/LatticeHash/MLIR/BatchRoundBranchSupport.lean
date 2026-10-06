/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.SLLVM.Cfg.Basic

namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM

/-- Relate two actual conditional terminators through their operand and
successor denotations. Poison in the branch condition remains UB. -/
theorem condBr_transport {Γ Δ : Ctxt SLLVM.Ty} {ss ds : List (List SLLVM.Ty)}
    {rs : List SLLVM.Ty} {α : Type}
    (V : Γ.Valuation) (W : Δ.Valuation)
    (c : Γ.Var (SLLVM.Ty.bitvec 1)) (d : Δ.Var (SLLVM.Ty.bitvec 1))
    (st sf : Target Γ ss) (dt df : Target Δ ds)
    (adapt : SuccArgs ss → SuccArgs ds)
    (hc : W d = V c)
    (ht : adapt (st.denote V) = dt.denote W)
    (hf : adapt (sf.denote V) = df.denote W)
    (K : (HVector TyDenote.toType rs ⊕ SuccArgs ds) → EffectM α) :
    (Terminator.denote (.condBr d dt df) W >>= K) =
      (Terminator.denote (.condBr c st sf) V >>= fun r =>
        K (r.map id adapt)) := by
  simp only [Terminator.denote_condBr, hc]
  cases h : V c using PoisonOr.casesOn' with
  | poison => rfl
  | value b =>
    by_cases hb : b = 1#1
    · simp [hb, ht]
    · simp [hb, hf]

end AgaveLatticeHash.MLIR.BatchRoundBranches

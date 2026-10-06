import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofPure
namespace AgaveLatticeHash.MLIR.BlockPrefix
open LeanMLIR SLLVM

theorem run_of_append_ret (p : BlockPrefix Γ Δ) (V : Γ.Valuation) (W : Δ.Valuation)
    (s : GlobalState)
    (h : StateT.run ((p.append (.term (.ret (.nil : HVector Δ.Var ([] : List SLLVM.Ty))) : BlockCom Δ Δ [] [])).denote V >>= pure) s =
      .value ((W, .inl ([]ₕ : HVector toType ([] : List SLLVM.Ty))), s)) :
    StateT.run (p.denote V) s = .value (W, s) := by
  rw [denote_append, bind_pure] at h
  cases hr : StateT.run (p.denote V) s with
  | poison =>
    simp only [EffectM.run_bind, hr, PoisonOr.poison_bind] at h
    exact False.elim (PoisonOr.poison_ne_value _ h)
  | value ws =>
    rcases ws with ⟨Z, t⟩
    simp only [EffectM.run_bind, hr, PoisonOr.value_bind, BlockCom.denote_term,
      Terminator.denote_ret, EffectM.run_pure, HVector.map] at h
    have hv := PoisonOr.value_inj.mp h
    cases hv
    rfl

end AgaveLatticeHash.MLIR.BlockPrefix

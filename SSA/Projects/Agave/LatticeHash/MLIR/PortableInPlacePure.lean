import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofPure
namespace AgaveLatticeHash.MLIR.BlockPrefix
open LeanMLIR SLLVM

theorem Renamed.pure {f : Γ.Hom Γ'} {g : Δ.Hom Δ'}
    {p : BlockPrefix Γ Δ} {q : BlockPrefix Γ' Δ'} (h : Renamed f p q g)
    (hp : p.Pure) : q.Pure := by
  induction h with
  | nil => exact .nil
  | var e h ih =>
    cases hp with
    | var he hp => exact .var he (ih hp)
  | var_semantic e e' _he hPure h ih =>
    cases hp with
    | var he hp => exact .var (hPure he) (ih hp)

end AgaveLatticeHash.MLIR.BlockPrefix

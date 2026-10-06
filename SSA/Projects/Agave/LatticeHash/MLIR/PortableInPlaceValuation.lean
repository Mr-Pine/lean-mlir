import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofPure
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM

theorem valuation_comap_vars {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} (vs : HVector Γ.Var ts) (V : Γ.Valuation) :
    V.comap (fun _ v => vs[v]) = Ctxt.Valuation.ofHVector (vs.map V) := by
  funext t v
  simp only [Ctxt.Valuation.comap, Ctxt.Valuation.ofHVector_apply, HVector.getElem_map]

end AgaveLatticeHash.MLIR

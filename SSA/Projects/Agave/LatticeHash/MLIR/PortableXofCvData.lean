/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofTailData
namespace AgaveLatticeHash.MLIR.PortableXof
open LeanMLIR SLLVM
set_option maxRecDepth 16384
def cvVars : Vector (preRound.middle.Var (SLLVM.Ty.bitvec 32)) 8 :=
  #v[⟨803, rfl⟩, ⟨801, rfl⟩, ⟨799, rfl⟩, ⟨797, rfl⟩, ⟨795, rfl⟩, ⟨793, rfl⟩, ⟨791, rfl⟩, ⟨789, rfl⟩]
def cvVar (i : Fin 8) : preRound.middle.Var (SLLVM.Ty.bitvec 32) := cvVars[i]
end AgaveLatticeHash.MLIR.PortableXof

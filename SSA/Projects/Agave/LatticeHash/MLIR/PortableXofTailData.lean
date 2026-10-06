/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofData
import SSA.Projects.Agave.LatticeHash.MLIR.PortableMemory
namespace AgaveLatticeHash.MLIR.PortableXof
open LeanMLIR SLLVM Firedancer Blake3Compression
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def resultVars : Vector (preRound.middle.Var (SLLVM.Ty.bitvec 32)) 16 :=
  #v[⟨47, rfl⟩, ⟨33, rfl⟩, ⟨19, rfl⟩, ⟨5, rfl⟩, ⟨0, rfl⟩, ⟨42, rfl⟩, ⟨28, rfl⟩, ⟨14, rfl⟩, ⟨16, rfl⟩, ⟨2, rfl⟩, ⟨44, rfl⟩, ⟨30, rfl⟩, ⟨31, rfl⟩, ⟨17, rfl⟩, ⟨3, rfl⟩, ⟨45, rfl⟩]

def resultVar (i : Fin 16) : preRound.middle.Var (SLLVM.Ty.bitvec 32) := resultVars[i]

structure TailEnv (V : preRound.middle.Valuation) (out : Pointer) : Prop where
  out : V ⟨863, rfl⟩ = .value out
  off4 : V ⟨857, rfl⟩ = .value (4 : BitVec 64)
  off8 : V ⟨856, rfl⟩ = .value (8 : BitVec 64)
  off12 : V ⟨855, rfl⟩ = .value (12 : BitVec 64)
  off16 : V ⟨854, rfl⟩ = .value (16 : BitVec 64)
  off20 : V ⟨853, rfl⟩ = .value (20 : BitVec 64)
  off24 : V ⟨852, rfl⟩ = .value (24 : BitVec 64)
  off28 : V ⟨851, rfl⟩ = .value (28 : BitVec 64)
  off32 : V ⟨850, rfl⟩ = .value (32 : BitVec 64)
  off36 : V ⟨849, rfl⟩ = .value (36 : BitVec 64)
  off40 : V ⟨848, rfl⟩ = .value (40 : BitVec 64)
  off44 : V ⟨847, rfl⟩ = .value (44 : BitVec 64)
  off48 : V ⟨846, rfl⟩ = .value (48 : BitVec 64)
  off52 : V ⟨845, rfl⟩ = .value (52 : BitVec 64)
  off56 : V ⟨844, rfl⟩ = .value (56 : BitVec 64)
  off60 : V ⟨843, rfl⟩ = .value (60 : BitVec 64)

/-- Every result SSA word is actually stored by the exact pre-compression tail. -/
theorem stored_results (i : Fin 16) : Stored (resultVar i) preRound.tail := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    repeat first
    | apply Stored.head
    | apply Stored.var

end AgaveLatticeHash.MLIR.PortableXof

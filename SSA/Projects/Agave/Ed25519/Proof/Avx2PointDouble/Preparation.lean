module

public import SSA.Projects.RIR.Semantics.Operations.Vector
public import SSA.Projects.RIR.Run.Vector
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

/-! Exact poison-aware semantics of the emitted preparation shuffle network.
The partial shuffle lanes intentionally contain poison; the final blend
selects only defined lanes. -/
namespace Agave.Ed25519.Avx2PointDouble
open LeanMLIR.RIR
@[expose] public section

abbrev Vec32 := Vector (BitVec 32) 8

def prepareBlock (a : Vec32) : Vec32 :=
  #v[a[0], a[1], a[2], a[3], a[4], a[0] + a[1], a[6], a[2] + a[3]]

def maskA : Vector (Option (Fin 16)) 8 :=
  #v[none, none, none, none, none, some 0, none, some 2]
def maskB : Vector (Option (Fin 16)) 8 :=
  #v[none, none, none, none, none, some 1, none, some 3]
def maskBlend : Vector (Option (Fin 16)) 8 :=
  #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15]

/-- Actual sequence at observation 0 registers 205,211,216,221 (and the
corresponding sequences for the other four input registers). -/
def prepareOperation (a : ⟦.vec 8 32⟧) : ⟦.vec 8 32⟧ :=
  let b := Operation.shufflevector maskB a (Ty.poisoned (.vec 8 32))
  let x := Operation.shufflevector maskA a (Ty.poisoned (.vec 8 32))
  let sum := Vector.zipWith (Operation.add {}) x b
  Operation.shufflevector maskBlend a sum

/-- None of the deliberately poisoned intermediate lanes reaches the square
input. This is unconditional: the additions use wrapping u32 semantics. -/
theorem prepareOperation_value (a : Vec32) :
    prepareOperation (Ty.wrap a) = Ty.wrap (prepareBlock a) := by
  ext i hi
  interval_cases i <;>
    simp [prepareOperation, maskA, maskB, maskBlend, prepareBlock,
      Operation.shufflevector, Operation.add, Ty.wrap_vec, Ty.poisoned_vec]

end
end Agave.Ed25519.Avx2PointDouble

import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.ScalarInstructions
import SSA.Projects.RIR.Run.Vector

set_option backward.isDefEq.respectTransparency false

/-! The exact packed ABDC/difference/sum network after the first product.
The boolean retains the emitted difference between flagged and unflagged
limb pairs. Temporary poison lanes remain present until their shuffle. -/
namespace Agave.Ed25519.Avx2PointAdd
open LeanMLIR.RIR

def diffSumVec (x : Vector (BitVec 32) 8) (even odd : BitVec 32) :
    Vector (BitVec 32) 8 :=
  #v[(even - x[0]) + x[1], x[1] + x[0],
     (odd - x[2]) + x[3], x[3] + x[2],
     (even - x[5]) + x[4], x[4] + x[5],
     (odd - x[7]) + x[6], x[6] + x[7]]

def diffSumInstructions (x : ⟦Ty.vec 8 32⟧) (signed : Bool) (even odd : BitVec 32) :
    ⟦Ty.vec 8 32⟧ :=
  let abdc := Operation.shufflevector
    #v[some 0, some 1, some 2, some 3, some 5, some 4, some 7, some 6]
    x (Ty.poisoned (.vec 8 32))
  let swapped := Operation.shufflevector
    #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7]
    x (Ty.poisoned (.vec 8 32))
  let constants : ⟦Ty.vec 8 32⟧ :=
    #v[.value even, .poison, .value odd, .poison,
       .value even, .poison, .value odd, .poison]
  let negated := Vector.zipWith (Operation.sub {nsw := signed}) constants abdc
  let picked := Operation.shufflevector
    #v[some 0, some 9, some 2, some 11, some 4, some 13, some 6, some 15] negated abdc
  Vector.zipWith (Operation.add {nsw := signed}) picked swapped

/-- Small input words discharge every signed-overflow flag in the exact
network; the mask-based scalar rules establish this premise for flagged pairs. -/
theorem diffSumInstructions_eq (x : Vector (BitVec 32) 8) (signed : Bool)
    (even odd : BitVec 32) (he : even.toNat < 2^28) (ho : odd.toNat < 2^28)
    (hx : ∀ i : Fin 8, (x[i]).toNat < 2^28) :
    diffSumInstructions (Ty.wrap x) signed even odd = Ty.wrap (diffSumVec x even odd) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [diffSumInstructions, diffSumVec, Operation.shufflevector, Ty.wrap_vec]
  · erw [sub32_small_value signed _ _ he (hx 0)]
    exact diff32_small_value signed _ _ _ he (hx 0) (hx 1)
  · exact add32_small_value signed _ _ (hx 1) (hx 0)
  · erw [sub32_small_value signed _ _ ho (hx 2)]
    exact diff32_small_value signed _ _ _ ho (hx 2) (hx 3)
  · exact add32_small_value signed _ _ (hx 3) (hx 2)
  · erw [sub32_small_value signed _ _ he (hx 5)]
    exact diff32_small_value signed _ _ _ he (hx 5) (hx 4)
  · exact add32_small_value signed _ _ (hx 4) (hx 5)
  · erw [sub32_small_value signed _ _ ho (hx 7)]
    exact diff32_small_value signed _ _ _ ho (hx 7) (hx 6)
  · exact add32_small_value signed _ _ (hx 6) (hx 7)

end Agave.Ed25519.Avx2PointAdd

/-- info: 'Agave.Ed25519.Avx2PointAdd.diffSumInstructions_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.diffSumInstructions_eq

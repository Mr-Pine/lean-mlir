import SSA.Projects.RIR.Run.Vector
import Mathlib.Tactic.IntervalCases

/-! The exact vector preparation network preceding the first multiplication
in the imported cached-add observations. Poison is retained in the temporary
lanes and is proved absent from the selected result. -/
namespace Agave.Ed25519.Avx2PointAdd
open LeanMLIR.RIR

abbrev PackedVec32 := Vector (BitVec 32) 8

def prepareVec (x : PackedVec32) (even odd : BitVec 32) : PackedVec32 :=
  #v[(even - x[0]) + x[1], x[1] + x[0],
     (odd - x[2]) + x[3], x[3] + x[2], x[4], x[5], x[6], x[7]]

def prepareInstructions (x : ⟦Ty.vec 8 32⟧) (even odd : BitVec 32) :
    ⟦Ty.vec 8 32⟧ :=
  let constants : ⟦Ty.vec 8 32⟧ :=
    #v[.value even, .poison, .value odd, .poison, .poison, .poison, .poison, .poison]
  let negated := Vector.zipWith (Operation.sub {}) constants x
  let swapped := Operation.shufflevector
    #v[some 1, some 0, some 3, some 2, none, none, none, none] x (Ty.poisoned (.vec 8 32))
  let picked := Operation.shufflevector
    #v[some 0, some 9, some 2, some 11, none, none, none, none] negated x
  let sums := Vector.zipWith (Operation.add {}) picked swapped
  Operation.shufflevector
    #v[some 0, some 1, some 2, some 3, some 12, some 13, some 14, some 15] sums x

/-- Exact execution of the five emitted sub/shuffle/add/shuffle operations for
one packed limb pair. The unused half of `swapped` is poison, as in the MLIR;
the final shuffle selects the original Z/T words instead. -/
theorem prepareInstructions_eq (x : PackedVec32) (even odd : BitVec 32) :
    prepareInstructions (Ty.wrap x) even odd = Ty.wrap (prepareVec x even odd) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [prepareInstructions, prepareVec, Operation.shufflevector,
      Operation.sub, Operation.add, Ty.wrap_vec]

def negateVec (x : PackedVec32) (even odd : BitVec 32) : PackedVec32 :=
  #v[x[1], x[0], x[3], x[2], x[4], even - x[5], x[6], odd - x[7]]

/-- The three emitted operations on the cached argument of subtraction. -/
def negateInstructions (x : ⟦Ty.vec 8 32⟧) (even odd : BitVec 32) :
    ⟦Ty.vec 8 32⟧ :=
  let swapped := Operation.shufflevector
    #v[some 1, some 0, some 3, some 2, some 4, some 5, some 6, some 7]
    x (Ty.poisoned (.vec 8 32))
  let constants : ⟦Ty.vec 8 32⟧ :=
    #v[.poison, .poison, .poison, .poison, .poison, .value even, .poison, .value odd]
  let negated := Vector.zipWith (Operation.sub {}) constants swapped
  Operation.shufflevector
    #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] swapped negated

theorem negateInstructions_eq (x : PackedVec32) (even odd : BitVec 32) :
    negateInstructions (Ty.wrap x) even odd = Ty.wrap (negateVec x even odd) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [negateInstructions, negateVec,
      Operation.sub, Ty.wrap_vec]

end Agave.Ed25519.Avx2PointAdd

/-- info: 'Agave.Ed25519.Avx2PointAdd.prepareInstructions_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.prepareInstructions_eq

/-- info: 'Agave.Ed25519.Avx2PointAdd.negateInstructions_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Agave.Ed25519.Avx2PointAdd.negateInstructions_eq

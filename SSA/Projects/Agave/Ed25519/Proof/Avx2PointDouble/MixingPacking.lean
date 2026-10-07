import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.PreparationPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.Algebra
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseRepresentation
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement

/-! Physical packing and the exact poison-bearing mixing network in bb18.
The arithmetic assumptions are the reduced input limbs; the lazy subtraction
and every machine-width bound are consequences of that invariant. -/
namespace Agave.Ed25519.Avx2PointDouble
open LeanMLIR.RIR

def coordinates (P : Avx2PointAdd.Point) : Coordinates := ![P.X, P.Y, P.Z, P.T]
def pointOf (p : Coordinates) : Avx2PointAdd.Point := ⟨p 0, p 1, p 2, p 3⟩
def packCoordinates (p : Coordinates) : Blocks := Avx2PointAdd.Phases.packPoint (pointOf p)
def doublePoint (P : Avx2PointAdd.Point) : Avx2PointAdd.Point := pointOf (output (coordinates P))

theorem coordinates_bounded {P : Avx2PointAdd.Point} (h : Avx2PointAdd.pointReduced P) :
    PointBound (coordinates P) := by
  intro e
  fin_cases e
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem pointOf_reduced {p : Coordinates} (h : PointBound p) :
    Avx2PointAdd.pointReduced (pointOf p) := ⟨h 0, h 1, h 2, h 3⟩

theorem doublePoint_reduced {P : Avx2PointAdd.Point}
    (h : Avx2PointAdd.pointReduced P) : Avx2PointAdd.pointReduced (doublePoint P) :=
  pointOf_reduced (output_bounded (coordinates_bounded h))

theorem pointOf_value (p : Coordinates) :
    Avx2PointAdd.pointValue (pointOf p) = values p := rfl

theorem doublePoint_value {P : Avx2PointAdd.Point} (h : Avx2PointAdd.pointReduced P) :
    Avx2PointAdd.pointValue (doublePoint P) =
      PointArithmetic.avx2Double (Avx2PointAdd.pointValue P) :=
  output_values (coordinates_bounded h)

/-- Repacking every physical word is lossless, without a range assumption. -/
theorem packCoordinates_blockCoordinates (a : Blocks) :
    packCoordinates (blockCoordinates a) = a := by
  funext k
  apply Vector.ext
  intro i hi
  fin_cases k <;> interval_cases i <;>
    simp [packCoordinates, pointOf, blockCoordinates, Avx2PointAdd.Phases.packPoint,
      Avx2PointAdd.Phases.evenIndex, Avx2PointAdd.Phases.oddIndex,
      Avx2PointAdd.word, Avx2FieldMul.Execution.unpackBlocks]

theorem blockCoordinates_packPoint {P : Avx2PointAdd.Point}
    (h : Avx2PointAdd.pointReduced P) :
    blockCoordinates (Avx2PointAdd.Phases.packPoint P) = coordinates P := by
  have h0 (i : Fin 10) : P.X i < 2 ^ 32 := Avx2PointAdd.reduced_lt_u32 h.1 i
  have h1 (i : Fin 10) : P.Y i < 2 ^ 32 := Avx2PointAdd.reduced_lt_u32 h.2.1 i
  have h2 (i : Fin 10) : P.Z i < 2 ^ 32 := Avx2PointAdd.reduced_lt_u32 h.2.2.1 i
  have h3 (i : Fin 10) : P.T i < 2 ^ 32 := Avx2PointAdd.reduced_lt_u32 h.2.2.2 i
  funext lane limb
  fin_cases lane <;> fin_cases limb <;>
    simp [blockCoordinates, Avx2FieldMul.Execution.unpackBlocks,
      Avx2PointAdd.Phases.packPoint, Avx2PointAdd.Phases.evenIndex,
      Avx2PointAdd.Phases.oddIndex, coordinates, Avx2PointAdd.word]
  all_goals first | exact h0 _ | exact h1 _ | exact h2 _ | exact h3 _

def mixBlock (a : Vec32) (even odd : BitVec 32) : Vec32 :=
  #v[a[0] + a[1], a[0] + (even - a[1]),
     a[2] + a[3], a[2] + (odd - a[3]),
     a[0] + (a[4] + a[4]) + (even - a[1]), a[0] + a[1] + a[5],
     a[2] + (a[6] + a[6]) + (odd - a[3]), a[2] + a[3] + a[7]]

def leftBlock (a : Vec32) : Vec32 := #v[a[4], a[0], a[6], a[2], a[4], a[0], a[6], a[2]]
def rightBlock (a : Vec32) : Vec32 := #v[a[5], a[1], a[7], a[3], a[1], a[5], a[3], a[7]]

def zeroPrefix : ⟦Ty.vec 8 32⟧ :=
  #v[.value 0, .value 0, .value 0, .value 0, .poison, .poison, .poison, .poison]
def zeroDifference : ⟦Ty.vec 8 32⟧ :=
  #v[.poison, .value 0, .poison, .value 0, .value 0, .poison, .value 0, .poison]
def lazyConstants (even odd : BitVec 32) : ⟦Ty.vec 8 32⟧ :=
  #v[.poison, .value even, .poison, .value odd, .value even, .poison, .value odd, .poison]
def zeroSum : ⟦Ty.vec 8 32⟧ :=
  #v[.value 0, .poison, .value 0, .poison, .poison, .value 0, .poison, .value 0]

def mixOperation (a : ⟦Ty.vec 8 32⟧) (even odd : BitVec 32) : ⟦Ty.vec 8 32⟧ :=
  let poison := Ty.poisoned (.vec 8 32)
  let x := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] a poison
  let y := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] a poison
  let twice := Vector.zipWith (Operation.shl {}) a
    (Ty.wrap (t := .vec 8 32) (#v[1, 1, 1, 1, 1, 1, 1, 1] : Vec32))
  let z := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] zeroPrefix twice
  let zt := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] z a
  let plus := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] y zeroDifference
  let neg := Vector.zipWith (Operation.sub {}) (lazyConstants even odd) y
  let minus := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] zeroSum neg
  Vector.zipWith (Operation.add {})
    (Vector.zipWith (Operation.add {}) (Vector.zipWith (Operation.add {}) plus x) zt) minus

/-- Deliberately poisoned lanes are discarded before either helper operand. -/
theorem mixOperation_value (a : Vec32) (even odd : BitVec 32) :
    mixOperation (Ty.wrap a) even odd = Ty.wrap (mixBlock a even odd) := by
  have twice (x : BitVec 32) : x <<< 1 = x + x := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.mul_two]
  have add_left_comm (x y z : BitVec 32) : x + (y + z) = y + (x + z) := by
    rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [mixOperation, zeroPrefix, zeroDifference, lazyConstants, zeroSum,
      mixBlock, Operation.shufflevector, Operation.add, Operation.sub,
      Operation.shl, Ty.wrap_vec, Ty.poisoned_vec, twice,
      BitVec.add_assoc, BitVec.add_comm, add_left_comm]

theorem leftBlock_shuffle (a : Vec32) :
    Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2]
      (Ty.wrap a) (Ty.poisoned (.vec 8 32)) = Ty.wrap (leftBlock a) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [leftBlock, Ty.wrap_vec]

theorem rightBlock_shuffle (a : Vec32) :
    Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7]
      (Ty.wrap a) (Ty.poisoned (.vec 8 32)) = Ty.wrap (rightBlock a) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [rightBlock, Ty.wrap_vec]

private theorem twoP_eq_twiceP (i : Fin 10) : twoP i = Avx2PointAdd.twiceP i := by
  fin_cases i <;> rfl

theorem mixBlock_packed {q : Coordinates} (hq : PointBound q) (k : Fin 5) :
    mixBlock (packCoordinates q k) (Avx2PointAdd.Phases.evenConstant k)
      (Avx2PointAdd.Phases.oddConstant k) = packCoordinates (mix q) k := by
  have hsub (i : Fin 10) :
      BitVec.ofNat 32 (twoP i) - BitVec.ofNat 32 (q 1 i) =
        BitVec.ofNat 32 (twoP i - q 1 i) :=
    BitVec.ofNat_sub_ofNat_of_le _ _
      (Avx2PointAdd.reduced_lt_u32 (pointOf_reduced hq).2.1 i)
      (reduced_le_twoP (hq 1) i)
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [mixBlock, packCoordinates, pointOf, Avx2PointAdd.Phases.packPoint,
      Avx2PointAdd.Phases.evenConstant, Avx2PointAdd.Phases.oddConstant,
      Avx2PointAdd.word, ← twoP_eq_twiceP, hsub, mix,
      ← BitVec.ofNat_add, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem leftBlock_packed (q : Coordinates) (k : Fin 5) :
    leftBlock (packCoordinates (mix q) k) = packCoordinates (left q) k := by
  rfl

theorem rightBlock_packed (q : Coordinates) (k : Fin 5) :
    rightBlock (packCoordinates (mix q) k) = packCoordinates (right q) k := by
  rfl

end Agave.Ed25519.Avx2PointDouble

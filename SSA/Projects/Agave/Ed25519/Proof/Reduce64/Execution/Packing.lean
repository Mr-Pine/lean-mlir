import SSA.Projects.RIR.Run.Vector
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Words
import Mathlib.Tactic.IntervalCases

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

section

-- Width equalities carried by bitcast must also reduce while the simplifier
-- checks implicit arguments, rather than only during ordinary elaboration.
attribute [local implicit_reducible] Ty.width

abbrev V4 := Vector (BitVec 64) 4
abbrev V8 := Vector (BitVec 32) 8
abbrev Columns4 := Fin 10 → V4

/-- Low 32 bits, exactly as selected by the emitted bitcast and shuffle. -/
def low32 (x : BitVec 64) : BitVec 32 := x.extractLsb' 0 32

/-- The physical `FieldElement2625x4` order is A,B for the even limb, A,B for
the odd limb, then C,D for the even limb and C,D for the odd limb. -/
def packPair (even odd : V4) : V8 :=
  #v[low32 even[0], low32 even[1], low32 odd[0], low32 odd[1],
     low32 even[2], low32 even[3], low32 odd[2], low32 odd[3]]

def reduceLanes (z : Columns4) (i : Fin 10) : V4 :=
  Vector.ofFn fun lane => Word.reduce (fun j => (z j)[lane]) i

def packedOutput (z : Columns4) (k : Fin 5) : V8 :=
  packPair (reduceLanes z ⟨2 * k, by omega⟩)
    (reduceLanes z ⟨2 * k + 1, by omega⟩)

def pairShuffle : Vector (Option (Fin 16)) 8 :=
  #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14]

def halfMask (m : BitVec 32) : ⟦Ty.vec 8 32⟧ :=
  #v[.value m, .poison, .value m, .poison,
     .value m, .poison, .value m, .poison]

/-- For defined source lanes, the actual bitcast semantics agrees with the
little-endian packed bits and produces no poisoned destination lane. -/
@[mlir_operation]
theorem bitcast_wrap {l w l' w' : Nat} (h : w * l = w' * l')
    (x : Vector (BitVec w) l) :
    Operation.bitcast (t := .vec l w) (t' := .vec l' w') h (Ty.wrap x) =
      Ty.wrap (Vector.ofFn fun j : Fin l' =>
        (BitVec.packLanes x).extractLsb' (j.val * w') w') := by
  ext i hi
  simp [Operation.bitcast, Ty.wrap_vec, Function.comp_def]

private theorem low32_extract (x : BitVec w) (start : Nat) :
    low32 (x.extractLsb' start 64) = x.extractLsb' start 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [low32, hi, show i < 64 by omega]

theorem low32_packLanes (x : V4) (i : Fin 4) :
    (BitVec.packLanes x).extractLsb' (i.val * 64) 32 = low32 x[i] := by
  rw [← low32_extract, BitVec.extractLsb'_packLanes x i.val i.isLt]
  rfl

@[simp, mlir_operation] theorem low32_packLanes_0 (x : V4) :
    (BitVec.packLanes x).extractLsb' 0 32 = low32 x[0] := by
  simpa using low32_packLanes x 0

@[simp, mlir_operation] theorem low32_packLanes_1 (x : V4) :
    (BitVec.packLanes x).extractLsb' 64 32 = low32 x[1] := by
  simpa using low32_packLanes x 1

@[simp, mlir_operation] theorem low32_packLanes_2 (x : V4) :
    (BitVec.packLanes x).extractLsb' 128 32 = low32 x[2] := by
  simpa using low32_packLanes x 2

@[simp, mlir_operation] theorem low32_packLanes_3 (x : V4) :
    (BitVec.packLanes x).extractLsb' 192 32 = low32 x[3] := by
  simpa using low32_packLanes x 3

@[simp] theorem bitcast64_lane0 (x : V4) :
    (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (x.map .value))[0] =
      .value (low32 x[0]) := by
  simp [Operation.bitcast, Function.comp_def]

@[simp] theorem bitcast64_lane2 (x : V4) :
    (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (x.map .value))[2] =
      .value (low32 x[1]) := by
  simp [Operation.bitcast, Function.comp_def]

@[simp] theorem bitcast64_lane4 (x : V4) :
    (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (x.map .value))[4] =
      .value (low32 x[2]) := by
  simp [Operation.bitcast, Function.comp_def]

@[simp] theorem bitcast64_lane6 (x : V4) :
    (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (x.map .value))[6] =
      .value (low32 x[3]) := by
  simp [Operation.bitcast, Function.comp_def]

theorem low32_mask (x : BitVec 64) (m : BitVec 32) :
    low32 (x &&& m.setWidth 64) = low32 x &&& m := by
  simp [low32, BitVec.extractLsb'_and, BitVec.extractLsb'_setWidth_of_le]

/-- Only the four even half-lanes are selected; all poison mask lanes are
discarded before the output is stored. -/
theorem shuffle_mask_left (a b : V4) (m : BitVec 32) :
    Operation.shufflevector pairShuffle
      (Vector.zipWith Operation.and
        (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (Ty.wrap a))
        (halfMask m))
      (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (Ty.wrap b)) =
      Ty.wrap (packPair (a.map (fun x => x &&& m.setWidth 64)) b) := by
  apply Vector.ext
  intro i hi
  have : i < 8 := hi
  interval_cases i <;>
    simp [pairShuffle, halfMask, Operation.shufflevector,
      Vector.getElem_zipWith, Operation.bitcast, Function.comp_def,
      Operation.and, packPair,
      Ty.wrap_vec, ← low32_mask]

theorem shuffle_mask_both (a b : V4) (m n : BitVec 32) :
    Operation.shufflevector pairShuffle
      (Vector.zipWith Operation.and
        (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (Ty.wrap a))
        (halfMask m))
      (Vector.zipWith Operation.and
        (Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) rfl (Ty.wrap b))
        (halfMask n)) =
      Ty.wrap (packPair (a.map (fun x => x &&& m.setWidth 64))
        (b.map (fun x => x &&& n.setWidth 64))) := by
  apply Vector.ext
  intro i hi
  have : i < 8 := hi
  interval_cases i <;>
    simp [pairShuffle, halfMask, Operation.shufflevector,
      Vector.getElem_zipWith, Operation.bitcast, Function.comp_def,
      Operation.and, packPair,
      Ty.wrap_vec, ← low32_mask]

/-- The output limb position inside the physical 8×32-bit register. -/
def physicalLane (odd : Bool) (lane : Fin 4) : Fin 8 :=
  ⟨(lane.val / 2) * 4 + (if odd then 2 else 0) + lane.val % 2, by
    split <;> omega⟩

theorem packPair_lane (a b : V4) (odd : Bool) (lane : Fin 4) :
    (packPair a b)[physicalLane odd lane] = low32 ((if odd then b else a)[lane]) := by
  cases odd <;> fin_cases lane <;> rfl

end
end Agave.Ed25519.Reduce64.Execution

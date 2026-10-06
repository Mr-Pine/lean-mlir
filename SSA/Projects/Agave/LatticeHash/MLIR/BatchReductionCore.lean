import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.TransposeReduction
import Mathlib.Tactic.IntervalCases

/-! Pure arithmetic of the compiler-emitted AVX2 output reduction. The caller
connects these operations to block 24; this file proves the shuffle/bitcast/add
network on arbitrary defined columns, independently of memory and control flow. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace AgaveLatticeHash.MLIR.BatchReduction
open LeanMLIR SLLVM
open InstCombine (LLVM)
abbrev Row8 := Vector (LLVM.IntW 32) 8
abbrev HalfRow := Vector (LLVM.IntW 16) 16
abbrev Words8 := Vector (BitVec 32) 8
abbrev Columns8 := Vector Words8 8

private theorem shuffle0 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 8, 1, 9, 4, 12, 5, 13] a b = #v[a[0], b[0], a[1], b[1], a[4], b[4], a[5], b[5]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle1 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 10, 3, 11, 6, 14, 7, 15] a b = #v[a[2], b[2], a[3], b[3], a[6], b[6], a[7], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle2 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 8, 9, 4, 5, 12, 13] a b = #v[a[0], a[1], b[0], b[1], a[4], a[5], b[4], b[5]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle3 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 3, 10, 11, 6, 7, 14, 15] a b = #v[a[2], a[3], b[2], b[3], a[6], a[7], b[6], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle4 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11] a b = #v[a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle5 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15] a b = #v[a[4], a[5], a[6], a[7], b[4], b[5], b[6], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

/-- The exact shuffle sequence %1470..%1493 (also %1521..%1544). -/
def shuffleRows8 (x0 x1 x2 x3 x4 x5 x6 x7 : Row8) : Vector Row8 8 :=
  let v1470 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 8, 1, 9, 4, 12, 5, 13] x0 x1
  let v1471 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 10, 3, 11, 6, 14, 7, 15] x0 x1
  let v1472 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 8, 1, 9, 4, 12, 5, 13] x2 x3
  let v1473 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 10, 3, 11, 6, 14, 7, 15] x2 x3
  let v1474 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 8, 1, 9, 4, 12, 5, 13] x4 x5
  let v1475 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 10, 3, 11, 6, 14, 7, 15] x4 x5
  let v1476 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 8, 1, 9, 4, 12, 5, 13] x6 x7
  let v1477 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 10, 3, 11, 6, 14, 7, 15] x6 x7
  let v1478 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 8, 9, 4, 5, 12, 13] v1470 v1472
  let v1479 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 3, 10, 11, 6, 7, 14, 15] v1470 v1472
  let v1480 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 8, 9, 4, 5, 12, 13] v1471 v1473
  let v1481 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 3, 10, 11, 6, 7, 14, 15] v1471 v1473
  let v1482 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 8, 9, 4, 5, 12, 13] v1474 v1476
  let v1483 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 3, 10, 11, 6, 7, 14, 15] v1474 v1476
  let v1484 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 8, 9, 4, 5, 12, 13] v1475 v1477
  let v1485 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 3, 10, 11, 6, 7, 14, 15] v1475 v1477
  let v1486 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11] v1478 v1482
  let v1487 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11] v1479 v1483
  let v1488 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11] v1480 v1484
  let v1489 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11] v1481 v1485
  let v1490 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15] v1478 v1482
  let v1491 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15] v1479 v1483
  let v1492 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15] v1480 v1484
  let v1493 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15] v1481 v1485
  #v[v1486, v1487, v1488, v1489, v1490, v1491, v1492, v1493]

/-- Mathematical rows: row r contains lane r from each input column. -/
def transposeRows8 (x0 x1 x2 x3 x4 x5 x6 x7 : Row8) : Vector Row8 8 :=
  Vector.ofFn fun r => #v[x0[r], x1[r], x2[r], x3[r], x4[r], x5[r], x6[r], x7[r]]

theorem shuffleRows8_transpose (x0 x1 x2 x3 x4 x5 x6 x7 : Row8) :
    shuffleRows8 x0 x1 x2 x3 x4 x5 x6 x7 = transposeRows8 x0 x1 x2 x3 x4 x5 x6 x7 := by
  simp only [shuffleRows8, shuffle0, shuffle1, shuffle2, shuffle3, shuffle4, shuffle5]
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-- The bitcast in each reduction summand. -/
def castHalves (x : Row8) : HalfRow :=
  bitcast (.vector 8 (.bitvec (.concrete 32))) (.vector 16 (.bitvec (.concrete 16))) x

/-- LLVM's wrapping vector add, with no overflow flags. -/
def addHalves (a b : HalfRow) : HalfRow :=
  Vector.ofFn fun i => InstCombine.binaryDenote (.add {}) a[i] b[i]

/-- Exact emitted addition order: row 1 plus row 0, followed by rows 2..7. -/
def sumRows8 (rows : Vector Row8 8) : HalfRow :=
  let s := addHalves (castHalves rows[1]) (castHalves rows[0])
  let s := addHalves s (castHalves rows[2])
  let s := addHalves s (castHalves rows[3])
  let s := addHalves s (castHalves rows[4])
  let s := addHalves s (castHalves rows[5])
  let s := addHalves s (castHalves rows[6])
  addHalves s (castHalves rows[7])

def reduce8 (x0 x1 x2 x3 x4 x5 x6 x7 : Row8) : HalfRow :=
  sumRows8 (shuffleRows8 x0 x1 x2 x3 x4 x5 x6 x7)

/-- Shuffle correctness also holds for poison-bearing input columns. -/
theorem reduce8_transpose (x0 x1 x2 x3 x4 x5 x6 x7 : Row8) :
    reduce8 x0 x1 x2 x3 x4 x5 x6 x7 =
      sumRows8 (transposeRows8 x0 x1 x2 x3 x4 x5 x6 x7) := by
  rw [reduce8, shuffleRows8_transpose]

/-- Low then high u16, in x86 little-endian lane order. -/
def halves32 (v : Words8) : Vector (BitVec 16) 16 :=
  Vector.ofFn fun i => v[i.val / 2]'(by omega) |>.extractLsb' (16 * (i.val % 2)) 16

private theorem packBits_half (v : Words8) (i : Fin 16) :
    (packBits v).extractLsb' (i.val * 16) 16 = (halves32 v)[i] := by
  simp only [Fin.getElem_fin, halves32, Vector.getElem_ofFn]
  have he := BitVec.extractLsb'_extractLsb'_add_of_le
    (x := packBits v) (s := (i.val / 2) * 32) (n := 32)
    (s' := 16 * (i.val % 2)) (n' := 16) (by omega)
  have hn : (i.val / 2) * 32 + 16 * (i.val % 2) = i.val * 16 := by omega
  rw [hn] at he
  refine he.symm.trans ?_
  simpa only [Fin.getElem_fin] using congrArg
    (fun x : BitVec 32 => x.extractLsb' (16 * (i.val % 2)) 16)
    (extract_packBits v ⟨i.val / 2, by omega⟩)

theorem castHalves_defined (v : Words8) :
    castHalves (v.map PoisonOr.value) = (halves32 v).map PoisonOr.value := by
  unfold castHalves
  rw [bitcast_of_defined]
  · apply Vector.ext
    intro i hi
    simp only [LLVM.Ty.unflatten, LLVM.Ty.width, BitVec.setWidth_eq,
      Vector.getElem_ofFn, Vector.getElem_map]
    change PoisonOr.value ((packBits v).extractLsb' (i * 16) 16) = _
    rw [packBits_half v ⟨i, hi⟩]
    rfl
  · intro i
    show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _

def transposedWords (cols : Columns8) : Vector Words8 8 :=
  Vector.ofFn fun row => Vector.ofFn fun col => cols[col][row]

theorem transpose_defined (cols : Columns8) :
    transposeRows8 (cols[0].map PoisonOr.value) (cols[1].map PoisonOr.value)
      (cols[2].map PoisonOr.value) (cols[3].map PoisonOr.value)
      (cols[4].map PoisonOr.value) (cols[5].map PoisonOr.value)
      (cols[6].map PoisonOr.value) (cols[7].map PoisonOr.value) =
    (transposedWords cols).map (fun row => row.map PoisonOr.value) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  interval_cases j <;> simp [transposeRows8, transposedWords]

/-- Eight independent message contributions, added modulo 2^16. -/
def sum8 (f : Fin 8 → BitVec 16) : BitVec 16 :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7

/-- Independent mathematical sum: each output half-word sums its matching
half-word across all eight message lanes. -/
def columnSum (cols : Columns8) : Vector (BitVec 16) 16 :=
  Vector.ofFn fun i => sum8 fun lane =>
    (cols[i.val / 2]'(by omega))[lane].extractLsb' (16 * (i.val % 2)) 16

theorem addHalves_defined (a b : Vector (BitVec 16) 16) :
    addHalves (a.map PoisonOr.value) (b.map PoisonOr.value) =
      (Vector.ofFn fun i : Fin 16 => a[i] + b[i]).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [addHalves, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map]
  rfl

end AgaveLatticeHash.MLIR.BatchReduction

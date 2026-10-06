import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.TransposeReduction
import Mathlib.Tactic.IntervalCases

/-! Pure arithmetic of the compiler-emitted AVX-512 output reduction in source
block bb12. Inputs are logical XOF columns, not the compiler's interleaved XOR
instruction order. The block proof separately connects these exact operations
to the generated CFG. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace AgaveLatticeHash.MLIR.BatchReduction16
open LeanMLIR SLLVM
open InstCombine (LLVM)
abbrev Row16 := Vector (LLVM.IntW 32) 16
abbrev HalfRow := Vector (LLVM.IntW 16) 32
abbrev Words16 := Vector (BitVec 32) 16
abbrev Columns16 := Vector Words16 16

private theorem shuffle0 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] a b = #v[a[0], a[1], a[2], a[3], a[8], a[9], a[10], a[11], b[0], b[1], b[2], b[3], b[8], b[9], b[10], b[11]] := by
  ext i hi
  change i < 16 at hi
  interval_cases i <;> rfl

private theorem shuffle1 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] a b = #v[a[4], a[5], a[6], a[7], a[12], a[13], a[14], a[15], b[4], b[5], b[6], b[7], b[12], b[13], b[14], b[15]] := by
  ext i hi
  change i < 16 at hi
  interval_cases i <;> rfl

private theorem shuffle2 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] a b = #v[a[0], b[0], a[1], b[1], a[4], b[4], a[5], b[5], a[8], b[8], a[9], b[9], a[12], b[12], a[13], b[13]] := by
  ext i hi
  change i < 16 at hi
  interval_cases i <;> rfl

private theorem shuffle3 (a b : Row16) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] a b = #v[a[2], b[2], a[3], b[3], a[6], b[6], a[7], b[7], a[10], b[10], a[11], b[11], a[14], b[14], a[15], b[15]] := by
  ext i hi
  change i < 16 at hi
  interval_cases i <;> rfl

/-- Exact emitted shuffles %2491..%2554. x0..x7 correspond to even-numbered
XOR results %2472..%2486; x8..x15 to odd-numbered results %2473..%2487. -/
def shuffleRows16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Row16) : Vector Row16 16 :=
  let v2491 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x0 x4
  let v2492 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x1 x5
  let v2493 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x2 x6
  let v2494 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x3 x7
  let v2495 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x0 x4
  let v2496 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x1 x5
  let v2497 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x2 x6
  let v2498 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x3 x7
  let v2499 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x8 x12
  let v2500 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x9 x13
  let v2501 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x10 x14
  let v2502 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] x11 x15
  let v2503 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x8 x12
  let v2504 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x9 x13
  let v2505 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x10 x14
  let v2506 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] x11 x15
  let v2507 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2491 v2499
  let v2508 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2492 v2500
  let v2509 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2493 v2501
  let v2510 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2494 v2502
  let v2511 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2495 v2503
  let v2512 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2496 v2504
  let v2513 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2497 v2505
  let v2514 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27] v2498 v2506
  let v2515 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2491 v2499
  let v2516 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2492 v2500
  let v2517 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2493 v2501
  let v2518 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2494 v2502
  let v2519 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2495 v2503
  let v2520 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2496 v2504
  let v2521 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2497 v2505
  let v2522 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31] v2498 v2506
  let v2523 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2507 v2509
  let v2524 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2508 v2510
  let v2525 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2507 v2509
  let v2526 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2508 v2510
  let v2527 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2511 v2513
  let v2528 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2512 v2514
  let v2529 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2511 v2513
  let v2530 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2512 v2514
  let v2531 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2515 v2517
  let v2532 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2516 v2518
  let v2533 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2515 v2517
  let v2534 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2516 v2518
  let v2535 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2519 v2521
  let v2536 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2520 v2522
  let v2537 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2519 v2521
  let v2538 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2520 v2522
  let v2539 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2523 v2524
  let v2540 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2523 v2524
  let v2541 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2525 v2526
  let v2542 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2525 v2526
  let v2543 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2527 v2528
  let v2544 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2527 v2528
  let v2545 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2529 v2530
  let v2546 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2529 v2530
  let v2547 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2531 v2532
  let v2548 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2531 v2532
  let v2549 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2533 v2534
  let v2550 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2533 v2534
  let v2551 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2535 v2536
  let v2552 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2535 v2536
  let v2553 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29] v2537 v2538
  let v2554 := LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31] v2537 v2538
  #v[v2539, v2540, v2541, v2542, v2543, v2544, v2545, v2546, v2547, v2548, v2549, v2550, v2551, v2552, v2553, v2554]

def transposeRows16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Row16) : Vector Row16 16 :=
  Vector.ofFn fun r => #v[x0[r], x1[r], x2[r], x3[r], x4[r], x5[r], x6[r], x7[r], x8[r], x9[r], x10[r], x11[r], x12[r], x13[r], x14[r], x15[r]]

theorem shuffleRows16_transpose (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Row16) :
    shuffleRows16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 = transposeRows16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by
  simp only [shuffleRows16, shuffle0, shuffle1, shuffle2, shuffle3]
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

def castHalves (x : Row16) : HalfRow :=
  bitcast (.vector 16 (.bitvec (.concrete 32))) (.vector 32 (.bitvec (.concrete 16))) x

def addHalves (a b : HalfRow) : HalfRow :=
  Vector.ofFn fun i => InstCombine.binaryDenote (.add {}) a[i] b[i]

/-- Exact emitted order: row 1 plus row 0, then rows 2 through 15. -/
def sumRows16 (rows : Vector Row16 16) : HalfRow :=
  let s := addHalves (castHalves rows[1]) (castHalves rows[0])
  let s := addHalves s (castHalves rows[2])
  let s := addHalves s (castHalves rows[3])
  let s := addHalves s (castHalves rows[4])
  let s := addHalves s (castHalves rows[5])
  let s := addHalves s (castHalves rows[6])
  let s := addHalves s (castHalves rows[7])
  let s := addHalves s (castHalves rows[8])
  let s := addHalves s (castHalves rows[9])
  let s := addHalves s (castHalves rows[10])
  let s := addHalves s (castHalves rows[11])
  let s := addHalves s (castHalves rows[12])
  let s := addHalves s (castHalves rows[13])
  let s := addHalves s (castHalves rows[14])
  addHalves s (castHalves rows[15])

def reduce16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Row16) : HalfRow :=
  sumRows16 (shuffleRows16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)

theorem reduce16_transpose (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Row16) :
    reduce16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 = sumRows16 (transposeRows16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) := by
  rw [reduce16, shuffleRows16_transpose]

/-- Low then high u16, in x86 little-endian lane order. -/
def halves32 (v : Words16) : Vector (BitVec 16) 32 :=
  Vector.ofFn fun i => v[i.val / 2]'(by omega) |>.extractLsb' (16 * (i.val % 2)) 16

private theorem packBits_half (v : Words16) (i : Fin 32) :
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

theorem castHalves_defined (v : Words16) :
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

def transposedWords (cols : Columns16) : Vector Words16 16 :=
  Vector.ofFn fun row => Vector.ofFn fun col => cols[col][row]

theorem transpose_defined (cols : Columns16) :
    transposeRows16 (cols[0].map PoisonOr.value) (cols[1].map PoisonOr.value) (cols[2].map PoisonOr.value) (cols[3].map PoisonOr.value)
      (cols[4].map PoisonOr.value) (cols[5].map PoisonOr.value) (cols[6].map PoisonOr.value) (cols[7].map PoisonOr.value)
      (cols[8].map PoisonOr.value) (cols[9].map PoisonOr.value) (cols[10].map PoisonOr.value) (cols[11].map PoisonOr.value)
      (cols[12].map PoisonOr.value) (cols[13].map PoisonOr.value) (cols[14].map PoisonOr.value) (cols[15].map PoisonOr.value) =
    (transposedWords cols).map (fun row => row.map PoisonOr.value) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  interval_cases j <;> simp [transposeRows16, transposedWords]

/-- Sixteen independent message contributions, added modulo 2^16. -/
def sum16 (f : Fin 16 → BitVec 16) : BitVec 16 :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15

def columnSum (cols : Columns16) : Vector (BitVec 16) 32 :=
  Vector.ofFn fun i => sum16 fun lane =>
    (cols[i.val / 2]'(by omega))[lane].extractLsb' (16 * (i.val % 2)) 16

theorem addHalves_defined (a b : Vector (BitVec 16) 32) :
    addHalves (a.map PoisonOr.value) (b.map PoisonOr.value) =
      (Vector.ofFn fun i : Fin 32 => a[i] + b[i]).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [addHalves, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map]
  rfl

end AgaveLatticeHash.MLIR.BatchReduction16

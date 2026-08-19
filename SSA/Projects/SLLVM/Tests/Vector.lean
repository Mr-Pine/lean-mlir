/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# SLLVM vector element access

Coverage for `llvm.extractelement`: the value it reads, the lane numbering it
reads from, its two poison cases, and the round trip against
`llvm.insertelement`.

The lane-order test is the one worth keeping. `extractelement` is how a value
leaves the vector domain -- `fd_r43x6_extract_limbs` is six of them off an
`<8 x i64>` -- so a disagreement between its numbering and the one
`llvm.mlir.constant`'s `dense<[...]>` uses would silently transpose a field
element's limbs, and every arithmetic test would still pass.
-/

namespace LeanMLIR.SLLVM.Tests
open LeanMLIR

/-- Run a closed pure program and read its single 64-bit result. Unlike the
memory tests', these programs allocate nothing, so they elaborate to `.pure`. -/
private def runPure (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64]) :
    PoisonOr (BitVec 64) :=
  (com.denote Ctxt.Valuation.nil).head

/-! ## Lane numbering

Lane `i` of `dense<[v0, ..., v7]>` is `vi`. Extracting all eight lanes of
`dense<[0, 1, ..., 7]>` and packing each into its own byte gives
`0x0706050403020100` exactly when the two agree lane for lane -- any
transposition, reversal or off-by-one shows up as a different constant. -/

def laneOrder : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<[0, 1, 2, 3, 4, 5, 6, 7]> : vector<8xi64>}> : () -> (vector<8xi64>)
      %i0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> (i64)
      %s0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> (i64)
      %e0 = "llvm.extractelement"(%v, %i0) : (vector<8xi64>, i64) -> (i64)
      %t0 = "llvm.shl"(%e0, %s0) : (i64, i64) -> (i64)
      %i1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
      %s1 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> (i64)
      %e1 = "llvm.extractelement"(%v, %i1) : (vector<8xi64>, i64) -> (i64)
      %t1 = "llvm.shl"(%e1, %s1) : (i64, i64) -> (i64)
      %i2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> (i64)
      %s2 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> (i64)
      %e2 = "llvm.extractelement"(%v, %i2) : (vector<8xi64>, i64) -> (i64)
      %t2 = "llvm.shl"(%e2, %s2) : (i64, i64) -> (i64)
      %i3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> (i64)
      %s3 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> (i64)
      %e3 = "llvm.extractelement"(%v, %i3) : (vector<8xi64>, i64) -> (i64)
      %t3 = "llvm.shl"(%e3, %s3) : (i64, i64) -> (i64)
      %i4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> (i64)
      %s4 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> (i64)
      %e4 = "llvm.extractelement"(%v, %i4) : (vector<8xi64>, i64) -> (i64)
      %t4 = "llvm.shl"(%e4, %s4) : (i64, i64) -> (i64)
      %i5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> (i64)
      %s5 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> (i64)
      %e5 = "llvm.extractelement"(%v, %i5) : (vector<8xi64>, i64) -> (i64)
      %t5 = "llvm.shl"(%e5, %s5) : (i64, i64) -> (i64)
      %i6 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> (i64)
      %s6 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> (i64)
      %e6 = "llvm.extractelement"(%v, %i6) : (vector<8xi64>, i64) -> (i64)
      %t6 = "llvm.shl"(%e6, %s6) : (i64, i64) -> (i64)
      %i7 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
      %s7 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> (i64)
      %e7 = "llvm.extractelement"(%v, %i7) : (vector<8xi64>, i64) -> (i64)
      %t7 = "llvm.shl"(%e7, %s7) : (i64, i64) -> (i64)
      %a1 = "llvm.or"(%t0, %t1) : (i64, i64) -> (i64)
      %a2 = "llvm.or"(%a1, %t2) : (i64, i64) -> (i64)
      %a3 = "llvm.or"(%a2, %t3) : (i64, i64) -> (i64)
      %a4 = "llvm.or"(%a3, %t4) : (i64, i64) -> (i64)
      %a5 = "llvm.or"(%a4, %t5) : (i64, i64) -> (i64)
      %a6 = "llvm.or"(%a5, %t6) : (i64, i64) -> (i64)
      %a7 = "llvm.or"(%a6, %t7) : (i64, i64) -> (i64)
      "llvm.return"(%a7) : (i64) -> ()
  }]

#guard runPure laneOrder == .value 0x0706050403020100#64

/-- The same claim at one lane, spelled out: lane 5 of `dense<[10, ..., 17]>`
is `15`. -/
def laneFive : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<[10, 11, 12, 13, 14, 15, 16, 17]> : vector<8xi64>}> : () -> (vector<8xi64>)
      %i = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> (i64)
      %r = "llvm.extractelement"(%v, %i) : (vector<8xi64>, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure laneFive == .value 15#64

/-! ## Poison

Per LLVM, an index that is out of range or itself poison yields poison. Note
the asymmetry with `insertelement`, which poisons the *whole vector* in the
same situation: here the result is a single element, so there is nothing wider
to poison. -/

/-- Index 8 of an 8-lane vector. -/
def outOfRange : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> (vector<8xi64>)
      %i = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> (i64)
      %r = "llvm.extractelement"(%v, %i) : (vector<8xi64>, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure outOfRange == .poison

/-- A negative index. `-1` as an `i64` is `2^64 - 1`, far past lane 7, so this
must be poison -- not lane 7, and not lane 0 by some truncation of the index
to three bits. -/
def negativeIndex : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<[10, 11, 12, 13, 14, 15, 16, 17]> : vector<8xi64>}> : () -> (vector<8xi64>)
      %i = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
      %r = "llvm.extractelement"(%v, %i) : (vector<8xi64>, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure negativeIndex == .poison

/-- A poison index. -/
def poisonIndex : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> (vector<8xi64>)
      %i = "llvm.mlir.poison"() : () -> (i64)
      %r = "llvm.extractelement"(%v, %i) : (vector<8xi64>, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure poisonIndex == .poison

/-- A poison lane, read at a perfectly good index. -/
def poisonLane : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.poison"() : () -> (vector<8xi64>)
      %i = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> (i64)
      %r = "llvm.extractelement"(%v, %i) : (vector<8xi64>, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure poisonLane == .poison

/-! ## Round trip against `insertelement` -/

/-- `extract (insert v 99 at 3) at 3 = 99`. -/
def roundTripSame : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> (vector<8xi64>)
      %x = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> (i64)
      %i = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> (i64)
      %w = "llvm.insertelement"(%v, %x, %i) : (vector<8xi64>, i64, i64) -> (vector<8xi64>)
      %r = "llvm.extractelement"(%w, %i) : (vector<8xi64>, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure roundTripSame == .value 99#64

/-- An insert at lane 3 leaves lane 4 alone. -/
def roundTripOther : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<7> : vector<8xi64>}> : () -> (vector<8xi64>)
      %x = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> (i64)
      %i = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> (i64)
      %j = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> (i64)
      %w = "llvm.insertelement"(%v, %x, %i) : (vector<8xi64>, i64, i64) -> (vector<8xi64>)
      %r = "llvm.extractelement"(%w, %j) : (vector<8xi64>, i64) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure roundTripOther == .value 7#64

/-! ## The index width is carried by the operation

MLIR emits `i32` indices for `insertelement` and `i64` for `extractelement`
within the same region, so neither is fixed. -/

def narrowIndex : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {
    ^entry():
      %v = "llvm.mlir.constant"() <{value = dense<[10, 11, 12, 13, 14, 15, 16, 17]> : vector<8xi64>}> : () -> (vector<8xi64>)
      %i = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> (i32)
      %r = "llvm.extractelement"(%v, %i) : (vector<8xi64>, i32) -> (i64)
      "llvm.return"(%r) : (i64) -> ()
  }]

#guard runPure narrowIndex == .value 15#64

end LeanMLIR.SLLVM.Tests

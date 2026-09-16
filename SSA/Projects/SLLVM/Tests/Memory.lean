/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# SLLVM memory semantics

Regression tests for the two defects the store used to have -- it `|||`-ed the
new value into the block instead of splicing it, and shifted it the wrong way
-- and coverage for the vector-typed load/store and the MLIR spellings of the
memory operations.
-/

namespace LeanMLIR.SLLVM.Tests

open LeanMLIR

/-- Run a closed program and read its single 64-bit result. The return type is
written out concretely rather than left as `⟦…⟧`, so that `BEq` is found. -/
private def runScalar (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64]) :
    Option (PoisonOr (BitVec 64)) :=
  ((com.denote Ctxt.Valuation.nil).run ⟨⟨0⟩, ⟨∅⟩, ∅⟩).toOption.map (fun r => r.1.head)

/-! ## A store overwrites

`*p = 7; *p = 2; return *p` must be `2`. With the old `|||` it was `7`. -/

def overwrite : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p  = "ptr.alloca"() <{elem_type = i64}> : () -> (!ptr)
    %c7 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
    %c2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> (i64)
    "ptr.store"(%p, %c7) : (!ptr, i64) -> ()
    "ptr.store"(%p, %c2) : (!ptr, i64) -> ()
    %v  = "ptr.load"(%p) : (!ptr) -> (i64)
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar overwrite == some (.value 2#64)

/-! ## A store at a non-zero offset lands at that offset

Writing `0xAB` at byte offset 1 of an 8-byte block and reading the whole block
must give `0xAB00`. With the old `>>>` the value was shifted off the bottom
and the block read back as `0`. -/

def offsetStore : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p   = "ptr.alloca"() <{elem_type = i64}> : () -> (!ptr)
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %ab  = "llvm.mlir.constant"() <{value = 171 : i8}> : () -> (i8)
    %p8  = "ptr.add"(%p, %one) : (!ptr, i64) -> (!ptr)
    "ptr.store"(%p8, %ab) : (!ptr, i8) -> ()
    %v   = "ptr.load"(%p) : (!ptr) -> (i64)
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar offsetStore == some (.value 0xAB00#64)

/-- A neighbouring store must not disturb what is already there. -/
def spliceKeepsNeighbour : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i64}> : () -> (!ptr)
    %one  = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %full = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> (i64)
    %zero = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> (i8)
    "ptr.store"(%p, %full) : (!ptr, i64) -> ()
    %p8   = "ptr.add"(%p, %one) : (!ptr, i64) -> (!ptr)
    "ptr.store"(%p8, %zero) : (!ptr, i8) -> ()
    %v    = "ptr.load"(%p) : (!ptr) -> (i64)
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar spliceKeepsNeighbour == some (.value 0xFFFFFFFFFFFF00FF#64)

/-! ## Vector load and store, in MLIR's own spelling

`llvm.store` writes `(value, ptr)` where SLLVM's signature is `(ptr, value)`,
and MLIR spells the pointer type `!llvm.ptr`. Both are accepted, as are the
`alignment`, `ordering` and `tbaa` attributes, which this model ignores. -/

def vecRoundTrip :
    Com SLLVM (Ctxt.ofList [SLLVM.Ty.arith (.vector 4 (.bitvec 64))]) .impure
      [SLLVM.Ty.arith (.vector 4 (.bitvec 64))] := [sllvm| {
  ^entry(%x: vector<4xi64>):
    %p = "ptr.alloca"() <{elem_type = i256}> : () -> (!llvm.ptr)
    "llvm.store"(%x, %p) <{alignment = 32 : i64, ordering = 0 : i64}> : (vector<4xi64>, !llvm.ptr) -> ()
    %v = "llvm.load"(%p) : (!llvm.ptr) -> (vector<4xi64>)
    "llvm.return"(%v) : (vector<4xi64>) -> ()
}]

private def runVec (x : Vector (PoisonOr (BitVec 64)) 4) :
    Option (Vector (PoisonOr (BitVec 64)) 4) :=
  ((vecRoundTrip.denote (x::ᵥCtxt.Valuation.nil)).run ⟨⟨0⟩, ⟨∅⟩, ∅⟩).toOption.map
    (fun r => r.1.head)

-- Lane `0` sits in the low bits, as LLVM lays a vector out in memory.
#guard
  let x : Vector (PoisonOr (BitVec 64)) 4 := #v[.value 1, .value 2, .value 3, .value 4]
  runVec x == some x

-- Storing a vector with a poison lane is UB, as storing a poison scalar is.
#guard (runVec #v[.value 1, .poison, .value 3, .value 4]).isNone

/-! ## `llvm.alloca`'s count operand

`Op.alloca` allocates a single element, so the MLIR spelling is accepted only
when its count operand is visibly the constant 1 -- anything else is refused
at elaboration, not silently dropped. -/

/--
error: llvm.alloca: the count operand %c is not the constant 1, which is the only count Op.alloca can represent
-/
#guard_msgs in
example := [sllvm| {
  ^entry():
    %c = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> (i32)
    %p = "llvm.alloca"(%c) <{alignment = 64 : i64, elem_type = i64}> : (i32) -> (!llvm.ptr)
    "llvm.return"() : () -> ()
}]

/-! ## `llvm.intr.memset`

The fill covers exactly `len` bytes at the pointer, and nothing outside it. -/

/-- 32 bytes; `0xff` written over the 8 bytes at offset 8, then read back. -/
def memsetFills : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i256}> : () -> (!ptr)
    %one  = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %len  = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> (i64)
    %ff   = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> (i8)
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%q, %ff, %len) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %v = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar memsetFills == some (.value (BitVec.allOnes 64))

/-- The same fill must leave the i64 below it, written before the memset,
alone: the range is `[off, off + len)`, not the whole block. -/
def memsetKeepsNeighbour : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i256}> : () -> (!ptr)
    %one  = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %len  = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> (i64)
    %ff   = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> (i8)
    %c7   = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
    "llvm.store"(%c7, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memset"(%q, %ff, %len) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %v = "llvm.load"(%p) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar memsetKeepsNeighbour == some (.value 7#64)

/-- A fill running past the end of the block is UB, as an out-of-range store
is: 8 bytes allocated, 16 written. -/
def memsetOutOfRange : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i64}> : () -> (!ptr)
    %len  = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> (i64)
    %ff   = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> (i8)
    "llvm.intr.memset"(%p, %ff, %len) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %v = "llvm.load"(%p) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard (runScalar memsetOutOfRange).isNone

/-! ## `llvm.intr.memcpy`

The copy moves exactly `len` bytes, and reads the source before writing the
destination -- so overlapping ranges, which LLVM leaves undefined, copy what
was there. -/

/-- 32 bytes; `7` written at offset 0, copied to offset 8, read back. -/
def memcpyMoves : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i256}> : () -> (!ptr)
    %one  = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %len  = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> (i64)
    %v    = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> (i64)
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%q, %p, %len) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %r = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard runScalar memcpyMoves == some (.value 7#64)

/-- ... and a copy that runs off the end of the source block is UB. -/
def memcpyOutOfRange : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i64}> : () -> (!ptr)
    %q    = "ptr.alloca"() <{elem_type = i64}> : () -> (!ptr)
    %len  = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> (i64)
    "llvm.intr.memcpy"(%q, %p, %len) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %r = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard (runScalar memcpyOutOfRange).isNone

end LeanMLIR.SLLVM.Tests

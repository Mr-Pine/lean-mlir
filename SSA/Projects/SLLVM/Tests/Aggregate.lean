/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# Aggregates in registers

An LLVM aggregate held in a register (`!llvm.array<5 x i64>`,
`!llvm.struct<…>`) is modelled by its flat, in-memory layout: a bitvector of
the aggregate's padded size, lowest-addressed field in the low bits. A
constant aggregate packs its lanes into that bitvector and `llvm.insertvalue`
splices a field into it.

The shape the tests below reproduce is the one `mlir-translate` emits for a
constant `fd_f25519_t` initialiser (`fd_f25519_sqrt_ratio`,
`fd_ed25519_point_frombytes`): a `dense<…>` array constant, an `undef` struct,
and two `insertvalue`s.
-/

namespace LeanMLIR.SLLVM.Tests.Aggregate
open LeanMLIR

/-- Run a closed pure program and read its single 64-bit result. -/
private def runPure (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64]) :
    PoisonOr (BitVec 64) :=
  (com.denote Ctxt.Valuation.nil).head

/-- The same for a program that allocates, which elaborates to `.impure`. -/
private def runScalar (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64]) :
    Option (PoisonOr (BitVec 64)) :=
  ((com.denote Ctxt.Valuation.nil).run ⟨⟨0⟩, ⟨∅⟩, ∅⟩).toOption.map (fun r => r.1.head)

/-- Lane `0` of a `dense<…>` array constant is its low 64 bits. -/
def constLane0 : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %c = "llvm.mlir.constant"() <{value = dense<[10, 11, 12, 13, 14]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %v = "llvm.trunc"(%c) : (i320) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runPure constLane0 == (.value 10#64)

/-- ... and lane `1` its next 64, i.e. the packing is little-endian by lane,
as `LLVM.Ty.flattenBV` lays a vector out. -/
def constLane1 : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %c  = "llvm.mlir.constant"() <{value = dense<[10, 11, 12, 13, 14]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %sh = "llvm.mlir.constant"() <{value = 64 : i320}> : () -> i320
    %s  = "llvm.lshr"(%c, %sh) : (i320, i320) -> i320
    %v  = "llvm.trunc"(%s) : (i320) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runPure constLane1 == (.value 11#64)

/-- The splat form: `dense<c>` is `c` in every lane. -/
def constSplat : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %c  = "llvm.mlir.constant"() <{value = dense<7> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %sh = "llvm.mlir.constant"() <{value = 256 : i320}> : () -> i320
    %s  = "llvm.lshr"(%c, %sh) : (i320, i320) -> i320
    %v  = "llvm.trunc"(%s) : (i320) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runPure constSplat == (.value 7#64)

/-- `insertvalue` into an `undef` aggregate, where the field covers the whole
aggregate: the result is the field, *not* poison. This is the shape the
artifacts use, so it is the one case where the flat model has to be exact
about poison rather than conservative. -/
def insertIntoUndef : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %c = "llvm.mlir.constant"() <{value = dense<[10, 11, 12, 13, 14]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %s = "llvm.insertvalue"(%u, %c) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %v = "llvm.trunc"(%s) : (i320) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runPure insertIntoUndef == (.value 10#64)

/-- A field at a non-zero offset: element `1` of an `array<2 x i64>` sits at
byte offset 8, so inserting there must leave element `0` alone. -/
def insertAtOffset : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %c = "llvm.mlir.constant"() <{value = dense<[10, 11]> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    %x = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> i64
    %r = "llvm.insertvalue"(%c, %x) <{position = array<i64: 1>}> : (!llvm.array<2 x i64>, i64) -> !llvm.array<2 x i64>
    %v = "llvm.trunc"(%r) : (i128) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runPure insertAtOffset == (.value 10#64)

/-- ... and must land in element `1`. -/
def insertAtOffsetHigh : Com SLLVM (∅ : Ctxt SLLVM.Ty) .pure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %c  = "llvm.mlir.constant"() <{value = dense<[10, 11]> : tensor<2xi64>}> : () -> !llvm.array<2 x i64>
    %x  = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> i64
    %r  = "llvm.insertvalue"(%c, %x) <{position = array<i64: 1>}> : (!llvm.array<2 x i64>, i64) -> !llvm.array<2 x i64>
    %sh = "llvm.mlir.constant"() <{value = 64 : i128}> : () -> i128
    %s  = "llvm.lshr"(%r, %sh) : (i128, i128) -> i128
    %v  = "llvm.trunc"(%s) : (i128) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runPure insertAtOffsetHigh == (.value 99#64)

/-- The verbatim artifact shape, end to end: the aggregate is built in
registers, stored, and one limb read back through a gep -- so the flat layout
the model gives it is the layout memory sees. -/
def artifactInitialiser : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = dense<[1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]> : tensor<5xi64>}> : () -> !llvm.array<5 x i64>
    %2 = "llvm.mlir.undef"() : () -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<"struct.fd_f25519", (array<5 x i64>)>, !llvm.array<5 x i64>) -> !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>
    %4 = "llvm.mlir.undef"() : () -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %5 = "llvm.insertvalue"(%4, %3) <{position = array<i64: 0>}> : (!llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, !llvm.struct<"struct.fd_f25519", (array<5 x i64>)>) -> !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>
    %p = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    "llvm.store"(%5, %p) <{alignment = 16 : i64, ordering = 0 : i64}> : (i320, !llvm.ptr) -> ()
    %k = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %q = "llvm.getelementptr"(%p, %k) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %v = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar artifactInitialiser == some (.value 2117202627021982#64)

end LeanMLIR.SLLVM.Tests.Aggregate

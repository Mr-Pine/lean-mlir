/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# llvm.getelementptr

`SLLVMOp.gep` covers the one gep shape the Firedancer ref extraction emits: a
single dynamic index scaled by an integer element type
(`rawConstantIndices = array<i32: -2147483648>`). The gep lines below carry
the artifact's exact attribute dict, `inbounds` included.
-/

namespace LeanMLIR.SLLVM.Tests.Gep
open LeanMLIR

private def runScalar (com : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64]) :
    Option (PoisonOr (BitVec 64)) :=
  ((com.denote Ctxt.Valuation.nil).run ⟨⟨0⟩, ⟨∅⟩, ∅⟩).toOption.map (fun r => r.1.head)

/-- Element 1 of an i64 pair, written and read back through the gep'd
pointer: the gep must land at byte offset 8, not 1. -/
def gepRoundTrip : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p   = "ptr.alloca"() <{elem_type = i128}> : () -> (!ptr)
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %a   = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> (i64)
    %b   = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> (i64)
    "llvm.store"(%a, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%b, %q) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %v = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar gepRoundTrip == some (.value 22#64)

/-- The store through the gep'd pointer must not disturb element 0. -/
def gepKeepsNeighbour : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p   = "ptr.alloca"() <{elem_type = i128}> : () -> (!ptr)
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %a   = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> (i64)
    %b   = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> (i64)
    "llvm.store"(%a, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%b, %q) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %v = "llvm.load"(%p) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

#guard runScalar gepKeepsNeighbour == some (.value 11#64)

/-- The `fd_ed25519_point_is_zero` gep shape: a struct of four 40-byte
fields, a dynamic index and a constant field index. Field 1 must land at
byte offset 40 -- checked by storing through the struct gep and loading
through a plain byte-offset gep. -/
def structGep : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i1280}> : () -> (!ptr)
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> (i64)
    %five = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> (i64)
    %v    = "llvm.mlir.constant"() <{value = 77 : i64}> : () -> (i64)
    %f1 = "llvm.getelementptr"(%p, %zero) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>, array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %f1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p, %five) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard runScalar structGep == some (.value 77#64)

/-- The avx512 point struct: three `vector<8xi64>` fields, 64 bytes each.
Field 1 must land at byte offset 64 (i.e. `i64` element 8), which needs the
vector's own size and alignment, not its element's. -/
def vectorStructGep : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p     = "ptr.alloca"() <{elem_type = i1536}> : () -> (!ptr)
    %zero  = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> (i64)
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> (i64)
    %v     = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> (i64)
    %f1 = "llvm.getelementptr"(%p, %zero) <{elem_type = !llvm.struct<"struct.fd_curve25519_edwards", (vector<8xi64>, vector<8xi64>, vector<8xi64>)>, inbounds, rawConstantIndices = array<i32: -2147483648, 1>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %f1) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p, %eight) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %r = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard runScalar vectorStructGep == some (.value 99#64)

-- A gep with no leading dynamic index must be rejected, not silently
-- mis-scaled.
/--
error: llvm.getelementptr: the first index must be the dynamic operand (`-2147483648` sentinel); constant-only geps are not supported
-/
#guard_msgs in
def gepConstIndex : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p   = "ptr.alloca"() <{elem_type = i128}> : () -> (!ptr)
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %q = "llvm.getelementptr"(%p, %one) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 0>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %v = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

/-- The `fd_f25519_set` gep shape, verbatim: `x->limb[k]` as a gep of
`array<5 x i64>` with *two* dynamic index operands, the leading one the
constant `0`. `foldGepZeroIndex` must rewrite it to the single-index `i64`
gep, so element 1 lands at byte offset 8. -/
def zeroLeadGep : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p    = "ptr.alloca"() <{elem_type = i320}> : () -> (!ptr)
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> (i64)
    %one  = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %a    = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> (i64)
    %b    = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> (i64)
    "llvm.store"(%a, %p) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p, %zero, %one) <{elem_type = !llvm.array<5 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    "llvm.store"(%b, %q) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %v = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %w = "llvm.load"(%p) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %r = "llvm.add"(%v, %w) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.return"(%r) : (i64) -> ()
}]

#guard runScalar zeroLeadGep == some (.value 33#64)

-- A two-operand gep whose leading index is *not* a visible zero must stay
-- rejected, not folded.
/--
error: Expected exactly 2 argument(s), but found 3
-/
#guard_msgs in
def twoDynGep : Com SLLVM (∅ : Ctxt SLLVM.Ty) .impure [SLLVM.Ty.bitvec 64] := [sllvm| {
  ^entry():
    %p   = "ptr.alloca"() <{elem_type = i320}> : () -> (!ptr)
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> (i64)
    %q = "llvm.getelementptr"(%p, %one, %one) <{elem_type = !llvm.array<5 x i64>, inbounds, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
    %v = "llvm.load"(%q) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
}]

end LeanMLIR.SLLVM.Tests.Gep

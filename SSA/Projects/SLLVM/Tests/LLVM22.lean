import SSA.Projects.SLLVM.Cfg

/-! Regression coverage for syntax emitted by LLVM/MLIR 22. -/
namespace LeanMLIR.SLLVM.Tests.LLVM22
open LeanMLIR
open InstCombine (LLVM)

example : ([mlir_attr_val|array<i32>] : MLIR.AST.AttrValue (φ := 0)) = MLIR.AST.AttrValue.array [mlir_type|i32] [] := rfl

def signedAdd : Com SLLVM (Ctxt.ofList [SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8])
    .pure [SLLVM.Ty.bitvec 8] := [sllvm| {
  ^entry(%a: i8, %b: i8):
    %r = "llvm.add"(%a, %b) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
}]

def unsignedAdd : Com SLLVM (Ctxt.ofList [SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8])
    .pure [SLLVM.Ty.bitvec 8] := [sllvm| {
  ^entry(%a: i8, %b: i8):
    %r = "llvm.add"(%a, %b) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
}]

example : (signedAdd.denote (Ctxt.Valuation.ofPair (PoisonOr.value 1#8) (PoisonOr.value 127#8))).head =
    PoisonOr.poison := by rfl
example : (unsignedAdd.denote (Ctxt.Valuation.ofPair (PoisonOr.value 1#8) (PoisonOr.value 127#8))).head =
    PoisonOr.value 128#8 := by rfl
example : (signedAdd.denote (Ctxt.Valuation.ofPair (PoisonOr.value 1#8) (PoisonOr.value 255#8))).head =
    PoisonOr.value 0#8 := by rfl
example : (unsignedAdd.denote (Ctxt.Valuation.ofPair (PoisonOr.value 1#8) (PoisonOr.value 255#8))).head =
    PoisonOr.poison := by rfl

/-- Indexing a four-word vector advances by 32 bytes, not by one word. -/
def vectorGep : Com SLLVM (Ctxt.ofList [SLLVM.Ty.ptr]) .pure [SLLVM.Ty.ptr] :=
  [sllvm| {
    ^entry(%p: !llvm.ptr):
      %q = "llvm.getelementptr"(%p)
        <{elem_type = vector<4xi64>, rawConstantIndices = array<i32: 2>}>
        : (!llvm.ptr) -> !llvm.ptr
      "llvm.return"(%q) : (!llvm.ptr) -> ()
  }]

example (p : Pointer) :
    (vectorGep.denote (Ctxt.Valuation.singleton (PoisonOr.value p : SLLVM.Ptr))).head =
      PoisonOr.value (p.withOffset 64) := by rfl

/-- Numeric SSA names are resolved consistently for arguments and results. -/
def bothFlags : Com SLLVM (Ctxt.ofList [SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8])
    .pure [SLLVM.Ty.bitvec 8] := [sllvm| {
  ^entry(%123: i8, %456: i8):
    %789 = "llvm.add"(%123, %456) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "llvm.return"(%789) : (i8) -> ()
}]

example : (bothFlags.denote (Ctxt.Valuation.ofPair (PoisonOr.value 1#8) (PoisonOr.value 127#8))).head =
    PoisonOr.poison := rfl
example : (bothFlags.denote (Ctxt.Valuation.ofPair (PoisonOr.value 1#8) (PoisonOr.value 255#8))).head =
    PoisonOr.poison := rfl
example : (bothFlags.denote (Ctxt.Valuation.ofPair (PoisonOr.value 1#8) (PoisonOr.value 2#8))).head =
    PoisonOr.value 3#8 := rfl

/--
error: llvm.getelementptr: unsupported vector element size i1; expected a multiple of 8 bits
-/
#guard_msgs in
def packedVectorGep : Com SLLVM (Ctxt.ofList [SLLVM.Ty.ptr]) .pure [SLLVM.Ty.ptr] :=
  [sllvm| {
    ^entry(%p: !llvm.ptr):
      %q = "llvm.getelementptr"(%p)
        <{elem_type = vector<8xi1>, rawConstantIndices = array<i32: 1>}>
        : (!llvm.ptr) -> !llvm.ptr
      "llvm.return"(%q) : (!llvm.ptr) -> ()
  }]

-- The same guard applies recursively inside aggregates.
/--
error: llvm.getelementptr: unsupported vector element size i9; expected a multiple of 8 bits
-/
#guard_msgs in
def packedAggregateGep : Com SLLVM (Ctxt.ofList [SLLVM.Ty.ptr]) .pure [SLLVM.Ty.ptr] :=
  [sllvm| {
    ^entry(%p: !llvm.ptr):
      %q = "llvm.getelementptr"(%p)
        <{elem_type = !llvm.array<2 x vector<8 x i9>>, rawConstantIndices = array<i32: 1>}>
        : (!llvm.ptr) -> !llvm.ptr
      "llvm.return"(%q) : (!llvm.ptr) -> ()
  }]

end LeanMLIR.SLLVM.Tests.LLVM22

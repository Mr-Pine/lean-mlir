module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Global
public import SSA.Projects.RIR.Semantics.Operations.InboundsGep
meta import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR.Tests.Syntax.InboundsGep

@[expose] public section

private def flagOp (bits : Int) : MLIR.Op :=
  ⟨"llvm.getelementptr", [], [], [], .mk [.mk "noWrapFlags" (.int bits (.int 32))]⟩

#guard Translate.gepAllNoWrapFlags (flagOp 7)
#guard !Translate.gepAllNoWrapFlags (flagOp 1)
#guard !Translate.gepAllNoWrapFlags (flagOp 2)
#guard !Translate.gepAllNoWrapFlags (flagOp 3)
#guard !Translate.gepAllNoWrapFlags (flagOp 4)
#guard !Translate.gepAllNoWrapFlags (flagOp 6)
#guard !Translate.gepAllNoWrapFlags (flagOp 15)

-- Exact shape of the NAF/table indexing instructions in agave_avx2_double_base.mlir.
mlir_def tableIndex := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

mlir_def wideIndex := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i128):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i128) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

mlir_def constantIndex := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.getelementptr"(%arg0) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

mlir_def foldedIndex := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%1) : (!llvm.ptr) -> ()
}

mlir_def mixedIndex := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = !llvm.array<4 x i64>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

-- Definitional AST equalities prevent constant folding from erasing flag semantics.
theorem constantIndex_uses_checked_gep : constantIndex.entry.body =
    [.gepInbounds ⟨0, rfl⟩ (.arg 0 rfl) [.constant 24]] := rfl
theorem foldedIndex_uses_checked_gep : foldedIndex.entry.body =
    [.const (3#64) ⟨0, rfl⟩,
     .gepInbounds ⟨1, rfl⟩ (.arg 0 rfl) [.constant 24]] := rfl
theorem mixedIndex_uses_checked_gep : mixedIndex.entry.body =
    [.gepInbounds ⟨0, rfl⟩ (.arg 0 rfl)
      [.constant 0, .scaled 8 (.arg 1 rfl)]] := rfl

/-- info: 'LeanMLIR.RIR.Tests.Syntax.InboundsGep.constantIndex_uses_checked_gep' does not depend on any axioms -/
#guard_msgs in
#print axioms constantIndex_uses_checked_gep
/-- info: 'LeanMLIR.RIR.Tests.Syntax.InboundsGep.foldedIndex_uses_checked_gep' does not depend on any axioms -/
#guard_msgs in
#print axioms foldedIndex_uses_checked_gep
/-- info: 'LeanMLIR.RIR.Tests.Syntax.InboundsGep.mixedIndex_uses_checked_gep' does not depend on any axioms -/
#guard_msgs in
#print axioms mixedIndex_uses_checked_gep

private def state : GlobalState := (⟨default, default⟩ : GlobalState).alloca 32
private def ptr (offset : BitVec 64) : Pointer := ⟨⟨0⟩, offset⟩
private def result (f : Func) (args : Vals f.Γ.args) (s : GlobalState := state) :
    Option (PoisonOr Pointer) :=
  match f.eval 1 args s with
  | .value (some vs, _) =>
    match f.tRets, vs with
    | [.ptr], .cons v .nil => some v
    | _, _ => none
  | _ => none

#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 3)) == some (.value (ptr 24))
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 4)) == some (.value (ptr 32))
#guard result tableIndex (tableIndex.args (.value (ptr 32)) (.value 0)) == some (.value (ptr 32))
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 5)) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 32)) (.value 1)) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 33)) (.value 0)) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 8)) (.value (-1))) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value (2^61))) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 0)) .poison) == some .poison
#guard result wideIndex (wideIndex.args (.value (ptr 0)) (.value (2^64))) == some .poison
#guard result constantIndex (constantIndex.args (.value (ptr 0))) == some (.value (ptr 24))
#guard result foldedIndex (foldedIndex.args (.value (ptr 0))) == some (.value (ptr 24))
#guard result constantIndex (constantIndex.args (.value (ptr 16))) == some .poison
#guard result foldedIndex (foldedIndex.args (.value (ptr 16))) == some .poison
#guard result mixedIndex (mixedIndex.args (.value (ptr 0)) (.value 4)) == some (.value (ptr 32))
#guard result mixedIndex (mixedIndex.args (.value (ptr 0)) (.value 5)) == some .poison
-- Deliberate restricted-domain behavior: absent allocations are not silently treated as live.
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 0)) ⟨default, default⟩ == some .poison
#guard result constantIndex (constantIndex.args (.value (ptr 0))) ⟨default, default⟩ == some .poison

-- The combined flags allow a negative *narrow* index multiplied by zero, but
-- wide negative truncation still violates nuw even if the final offset is zero.
#guard Operation.gepInboundsIndex 0 (.value (-1 : BitVec 32)) == .value 0
#guard Operation.gepInboundsIndex 0 (.value (-1 : BitVec 128)) == .poison

example (g : ByteGlobal) (id : BlockId) (m : MemoryState)
    (hlive : g.Present id m) (hsize : g.length < 2^63)
    (offsets : List Int)
    (hwithin : Operation.GepInboundsOffsets g.length 0 offsets) :
    Operation.gepInboundsLive m (.value (g.address id)) (offsets.map .value) =
      .value ((g.address id).add (BitVec.ofInt 64 offsets.sum)) := by
  apply Operation.gepInboundsLive_eq (ptr := g.address id)
    (block := ⟨g.length, g.bytes⟩) hlive hsize
  simpa [ByteGlobal.address] using hwithin

/-- error: ^bb0: %0 = "llvm.getelementptr"(%arg0) : (!llvm.ptr) -> !llvm.ptr: inbounds GEP constant indices must be nonnegative and fit signed i64 -/
#guard_msgs in
mlir_def rejectNegativeConstant := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.getelementptr"(%arg0) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

/-- error: ^bb0: %1 = "llvm.getelementptr"(%arg0, %0) : (!llvm.ptr, i128) -> !llvm.ptr: inbounds GEP constant indices must be nonnegative and fit signed i64 -/
#guard_msgs in
mlir_def rejectWideFoldedConstant := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 18446744073709551616 : i128}> : () -> i128
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i128) -> !llvm.ptr
    "llvm.return"(%1) : (!llvm.ptr) -> ()
}

/-- error: ^bb0: %1 = "llvm.getelementptr"(%arg0, %0) : (!llvm.ptr, i64) -> !llvm.ptr: inbounds GEP constant byte offset must be nonnegative and fit signed i64 -/
#guard_msgs in
mlir_def rejectScaledConstantOverflow := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1152921504606846976 : i64}> : () -> i64
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%1) : (!llvm.ptr) -> ()
}

/-- error: ^bb0: %0 = "llvm.getelementptr"(%arg0) : (!llvm.ptr) -> !llvm.ptr: GEP flag combination is not supported -/
#guard_msgs in
mlir_def rejectUnsupportedConstantFlags := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.getelementptr"(%arg0) <{elem_type = i64, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.InboundsGep

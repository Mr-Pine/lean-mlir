module

public import SSA.Projects.RIR.Syntax.Elab
meta import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR.Tests.Syntax.DynamicGep

@[expose] public section

mlir_def signedIndex := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i32):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

mlir_def wideIndex := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i128):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i128) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

mlir_def nested := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64, %arg2: i32):
    %0 = "llvm.getelementptr"(%arg0, %arg1, %arg2) <{elem_type = !llvm.struct<(i8, array<2 x i64>)>, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i32) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

-- SSA constants produced by llvm-import are still the existing constant lift.
mlir_def folded := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%1) : (!llvm.ptr) -> ()
}

example : folded.entry.body =
    [.const (3#64) ⟨0, rfl⟩,
     .unop (.gepConst 24) ⟨1, rfl⟩ (.arg 0 rfl)] := rfl

mlir_def negativeConstant := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i8
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i8) -> !llvm.ptr
    "llvm.return"(%1) : (!llvm.ptr) -> ()
}

mlir_def zeroLengthArray := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = !llvm.array<0 x i32>, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

private def p (off : BitVec 64) : Pointer := ⟨⟨7⟩, off⟩
private def result (f : Func) (args : Vals f.Γ.args) : Option (PoisonOr Pointer) :=
  match f.eval 1 args ⟨default, default⟩ with
  | .value (some vs, _) =>
    match f.tRets, vs with
    | [.ptr], .cons v .nil => some v
    | _, _ => none
  | _ => none

#guard result signedIndex (signedIndex.args (.value (p 16)) (.value (-1))) == some (.value (p 8))
#guard result signedIndex (signedIndex.args (.value (p 0)) (.value (-1))) == some (.value (p (-8)))
#guard result signedIndex (signedIndex.args (.value (p (-1))) (.value 1)) == some (.value (p 7))
#guard result signedIndex (signedIndex.args (.value (p 8)) .poison) == some .poison
#guard result signedIndex (signedIndex.args .poison (.value 0)) == some .poison
-- High index bits are truncated before multiplication; multiplication may wrap.
#guard result wideIndex (wideIndex.args (.value (p 0)) (.value (2^64 + 1))) == some (.value (p 8))
#guard result wideIndex (wideIndex.args (.value (p 0)) (.value (2^61 + 1))) == some (.value (p 8))
#guard result wideIndex (wideIndex.args (.value (p 16)) (.value (-1))) == some (.value (p 8))
-- sizeof(struct)=24, field 1 offset=8, element stride=8; out-of-type-bound indices are legal.
#guard result nested (nested.args (.value (p 100)) (.value (-1)) (.value 3)) == some (.value (p 108))
#guard result negativeConstant (negativeConstant.args (.value (p 16))) == some (.value (p 8))
#guard result zeroLengthArray (zeroLengthArray.args (.value (p 0)) (.value 3)) == some (.value (p 12))

-- The new semantics never uses the legacy unsigned-overflow poison rule.
example (base : Pointer) (index : BitVec 32) :
    Operation.gepUnflagged (.value base) [Operation.gepIndex 8 (.value index)] =
      .value (base.add (BitVec.ofInt 64 index.toInt * 8)) := by
  simp [Operation.gepUnflagged, Operation.gepIndex, List.foldlM]

private def flagOp (value : MLIR.AttrValue) : MLIR.Op :=
  ⟨"llvm.getelementptr", [], [], [], .mk [.mk "noWrapFlags" value]⟩

#guard Translate.gepHasFlags (flagOp (.opaque_ "llvm.GEPNoWrapFlags" "nusw"))
#guard Translate.gepHasFlags (flagOp (.opaque_ "llvm.GEPNoWrapFlags" "nuw"))
#guard !Translate.gepHasFlags (flagOp (.opaque_ "llvm.GEPNoWrapFlags" "none"))

/-- error: ^bb0: %0 = "llvm.getelementptr"(%arg0, %arg1) : (!llvm.ptr, i64) -> !llvm.ptr: dynamic or signed GEP with inbounds/nusw/nuw/inrange is not supported -/
#guard_msgs in
mlir_def rejectInbounds := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i8, noWrapFlags = #llvm.GEPNoWrapFlags<inbounds>, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

/-- error: ^bb0: %0 = "llvm.getelementptr"(%arg0, %arg1) : (!llvm.ptr, i32) -> !llvm.ptr: structure GEP index must be constant -/
#guard_msgs in
mlir_def rejectDynamicStruct := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i32):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

/-- error: ^bb0: %0 = "llvm.getelementptr"(%arg0) : (!llvm.ptr) -> !llvm.ptr: struct field index 2 out of range -/
#guard_msgs in
mlir_def rejectOutOfRangeStruct := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.getelementptr"(%arg0) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: 0, 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.DynamicGep

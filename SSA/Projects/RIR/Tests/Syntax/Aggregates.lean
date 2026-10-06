module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Syntax.Translate

namespace LeanMLIR.RIR.Tests.Syntax.Aggregates

@[expose] public section

mlir_def nestedExtract := {
  ^bb0(%arg0: !llvm.struct<(i8, array<2 x struct<(i16, i32)>>)>):
    %0 = "llvm.extractvalue"(%arg0) <{position = array<i64: 1, 1, 0>}> : (!llvm.struct<(i8, array<2 x struct<(i16, i32)>>)>) -> i16
    "llvm.return"(%0) : (i16) -> ()
}

mlir_def nestedInsert := {
  ^bb0(%arg0: !llvm.struct<(i8, array<2 x struct<(i16, i32)>>)>, %arg1: i16):
    %0 = "llvm.insertvalue"(%arg0, %arg1) <{position = array<i64: 1, 1, 0>}> : (!llvm.struct<(i8, array<2 x struct<(i16, i32)>>)>, i16) -> !llvm.struct<(i8, array<2 x struct<(i16, i32)>>)>
    "llvm.return"(%0) : (!llvm.struct<(i8, array<2 x struct<(i16, i32)>>)>) -> ()
}

mlir_def singleton := {
  ^bb0(%arg0: !llvm.struct<(i32)>, %arg1: i32):
    %0 = "llvm.insertvalue"(%arg0, %arg1) <{position = array<i64: 0>}> : (!llvm.struct<(i32)>, i32) -> !llvm.struct<(i32)>
    %1 = "llvm.extractvalue"(%0) <{position = array<i64: 0>}> : (!llvm.struct<(i32)>) -> i32
    "llvm.return"(%1) : (i32) -> ()
}

private def runOne (f : Func) (a : Vals f.Γ.args) (t : Ty)
    (h : f.tRets = [t]) : Option ⟦t⟧ :=
  match f.eval 1 a ⟨default, default⟩ with
  | .value (some vs, _) => match h ▸ vs with
    | .cons v .nil => some v
  | _ => none

abbrev nestedTy : Ty := .struct [.bv 8, .array 2 (.struct [.bv 16, .bv 32])]
def mixed : ⟦nestedTy⟧ := (.poison, #v[(.poison, .value 11#32), (.value 7#16, .poison)])

-- Unrelated poison does not contaminate the selected component.
#guard runOne nestedExtract (nestedExtract.args mixed) (.bv 16) rfl == some (.value 7#16)
-- Insertion preserves every sibling, including poisoned siblings.
#guard runOne nestedInsert (nestedInsert.args mixed (.value 9#16)) nestedTy rfl ==
  some (.poison, #v[(.poison, .value 11#32), (.value 9#16, .poison)])
-- A poison component is replaceable, and a poison inserted value stays local.
#guard runOne singleton (singleton.args .poison (.value 42#32)) (.bv 32) rfl == some (.value 42#32)
#guard runOne nestedInsert (nestedInsert.args mixed .poison) nestedTy rfl ==
  some (.poison, #v[(.poison, .value 11#32), (.poison, .poison)])

private def rejects (v : Except String α) : Bool :=
  match v with
  | .error _ => true
  | .ok _ => false

#guard rejects (Translate.aggregatePath nestedTy [-1])
#guard rejects (Translate.aggregatePath nestedTy [2])
#guard rejects (Translate.aggregatePath nestedTy [1, 2])
#guard rejects (Translate.aggregatePath nestedTy [1, 0, 2])
#guard rejects (Translate.aggregatePath nestedTy [0, 0])
#guard rejects (Translate.aggregatePath (.array 0 (.bv 8)) [0])
#guard rejects (Translate.aggregatePath (.struct []) [0])
#guard rejects (Translate.aggregatePath (.vec 4 32) [0])

/-- error: ^bb0: %0 = "llvm.extractvalue"(%arg0) : (!llvm.struct<(i32)>) -> i64: selected aggregate type does not match result type -/
#guard_msgs in
mlir_def wrongExtractType := {
  ^bb0(%arg0: !llvm.struct<(i32)>):
    %0 = "llvm.extractvalue"(%arg0) <{position = array<i64: 0>}> : (!llvm.struct<(i32)>) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/-- error: ^bb0: %0 = "llvm.insertvalue"(%arg0, %arg1) : (!llvm.struct<(i32)>, i64) -> !llvm.struct<(i32)>: selected aggregate type does not match inserted value type -/
#guard_msgs in
mlir_def wrongInsertType := {
  ^bb0(%arg0: !llvm.struct<(i32)>, %arg1: i64):
    %0 = "llvm.insertvalue"(%arg0, %arg1) <{position = array<i64: 0>}> : (!llvm.struct<(i32)>, i64) -> !llvm.struct<(i32)>
    "llvm.return"(%0) : (!llvm.struct<(i32)>) -> ()
}

/-- error: ^bb0: %0 = "llvm.extractvalue"(%arg0) : (!llvm.struct<(i32)>) -> i32: structure index out of range -/
#guard_msgs in
mlir_def badIndex := {
  ^bb0(%arg0: !llvm.struct<(i32)>):
    %0 = "llvm.extractvalue"(%arg0) <{position = array<i64: 1>}> : (!llvm.struct<(i32)>) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.Aggregates

namespace LeanMLIR.RIR.Tests.Syntax.Aggregates

/-- error: ^bb0: %0 = "llvm.insertvalue"(%arg0, %arg1) : (!llvm.struct<(i32)>, i32) -> !llvm.struct<(i64)>: aggregate operand and result types must agree -/
#guard_msgs in
mlir_def wrongAggregateResult := {
  ^bb0(%arg0: !llvm.struct<(i32)>, %arg1: i32):
    %0 = "llvm.insertvalue"(%arg0, %arg1) <{position = array<i64: 0>}> : (!llvm.struct<(i32)>, i32) -> !llvm.struct<(i64)>
    "llvm.return"(%0) : (!llvm.struct<(i64)>) -> ()
}

/-- error: ^bb0: %0 = "llvm.extractvalue"(%arg0) : (!llvm.struct<(i32)>) -> i32: aggregate position must be nonempty -/
#guard_msgs in
mlir_def emptyPosition := {
  ^bb0(%arg0: !llvm.struct<(i32)>):
    %0 = "llvm.extractvalue"(%arg0) <{position = array<i64>}> : (!llvm.struct<(i32)>) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

#print axioms AggregatePath.get_set

end LeanMLIR.RIR.Tests.Syntax.Aggregates

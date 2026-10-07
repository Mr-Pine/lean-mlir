module

public import SSA.Projects.RIR.Syntax.Elab
import all SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.Func

/-! Pointer `icmp` in the exact SHA-512 dispatcher uses scalar `!llvm.ptr` operands.
Test translation, execution, same-allocation offset equality, poison and simplifier support.
RIR does not assign addresses or an ordering to allocation blocks, so a comparison across
allocation identities is poison. -/

namespace LeanMLIR.RIR.Tests.Syntax.PointerCompare

@[expose] public section

mlir_def ptrEq := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

mlir_def ptrNe := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 1 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

example (a b : PoisonOr Pointer) (s : GlobalState) :
    ptrEq.eval 1 (ptrEq.args a b) s =
      .value (some (.cons (Operation.ptrCmp false a b) .nil), s) := rfl

example (a b : PoisonOr Pointer) (s : GlobalState) :
    ptrNe.eval 1 (ptrNe.args a b) s =
      .value (some (.cons (Operation.ptrCmp true a b) .nil), s) := rfl

private def out (f : Func) (args : Vals f.Γ.args) (h : f.tRets = [.bv 1]) :
    Option (PoisonOr (BitVec 1)) :=
  match f.eval 1 args ⟨default, default⟩ with
  | .value (some vs, _) => match h ▸ vs with
    | .cons v .nil => some v
  | _ => none

-- These blocks need not exist in the empty memory: comparison does not dereference.
private def p : Pointer := ⟨⟨17⟩, 64#64⟩
private def otherBlock : Pointer := ⟨⟨18⟩, 64#64⟩
private def otherOffset : Pointer := ⟨⟨17⟩, 65#64⟩

#guard out ptrEq (ptrEq.args (.value p) (.value p)) rfl == some (.value 1#1)
#guard out ptrNe (ptrNe.args (.value p) (.value p)) rfl == some (.value 0#1)
#guard out ptrEq (ptrEq.args (.value p) (.value otherBlock)) rfl == some .poison
#guard out ptrNe (ptrNe.args (.value p) (.value otherBlock)) rfl == some .poison
#guard out ptrEq (ptrEq.args (.value p) (.value otherOffset)) rfl == some (.value 0#1)
#guard out ptrNe (ptrNe.args (.value p) (.value otherOffset)) rfl == some (.value 1#1)
#guard out ptrEq (ptrEq.args .poison (.value p)) rfl == some .poison
#guard out ptrEq (ptrEq.args (.value p) .poison) rfl == some .poison
#guard out ptrNe (ptrNe.args .poison (.value p)) rfl == some .poison
#guard out ptrNe (ptrNe.args (.value p) .poison) rfl == some .poison
#guard out ptrEq (ptrEq.args .poison .poison) rfl == some .poison
#guard out ptrNe (ptrNe.args .poison .poison) rfl == some .poison

example (a b : Pointer) (hid : a.id = b.id) :
    Operation.ptrCmp false (.value a) (.value b) =
      .value (BitVec.ofBool (decide (a.offset = b.offset))) := by
  simp only [mlir_operation, hid, ↓reduceIte, Bool.false_eq_true]

example (a b : Pointer) (hid : a.id = b.id) :
    Operation.ptrCmp true (.value a) (.value b) =
      .value (BitVec.ofBool (decide (a.offset ≠ b.offset))) := by
  simp only [mlir_operation, hid, ↓reduceIte]

example (a b : Pointer) (hid : a.id ≠ b.id) (isNe : Bool) :
    Operation.ptrCmp isNe (.value a) (.value b) = .poison := by
  simp only [mlir_operation, hid, ↓reduceIte]

example (isNe : Bool) (p : PoisonOr Pointer) :
    Operation.ptrCmp isNe .poison p = .poison := by
  simp only [mlir_operation]

example (isNe : Bool) (p : PoisonOr Pointer) :
    Operation.ptrCmp isNe p .poison = .poison := by
  simp only [mlir_operation]

example (p : Pointer) : Operation.ptrCmp false (.value p) (.value p) = .value 1#1 := by
  simp [mlir_operation]

example (p : Pointer) : Operation.ptrCmp true (.value p) (.value p) = .value 0#1 := by
  simp [mlir_operation]

-- This is the shape used by the SHA dispatcher: its cursor and end pointer are
-- both obtained by adding offsets to the same input pointer.
example (base : Pointer) (cursorOffset endOffset : BitVec 64) :
    Operation.ptrCmp false (.value (base.add cursorOffset)) (.value (base.add endOffset)) =
      .value (BitVec.ofBool (decide ((base.add cursorOffset).offset =
        (base.add endOffset).offset))) := by
  simp only [mlir_operation, Pointer.add_id, ↓reduceIte, Bool.false_eq_true]

/-- error: ^bb0: %0 = "llvm.icmp"(%arg0, %arg1) : (!llvm.ptr, !llvm.ptr) -> i1: ordered pointer comparisons are not supported -/
#guard_msgs in
mlir_def signedPointerOrder := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 2 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

/-- error: ^bb0: %0 = "llvm.icmp"(%arg0, %arg1) : (!llvm.ptr, !llvm.ptr) -> i1: ordered pointer comparisons are not supported -/
#guard_msgs in
mlir_def unsignedPointerOrder := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 6 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

/-- error: ^bb0: %0 = "llvm.icmp"(%arg0, %arg1) : (!llvm.ptr, i64) -> i1: the operand types differ -/
#guard_msgs in
mlir_def mixedPointerInteger := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 0 : i64}> : (!llvm.ptr, i64) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

/-- error: ^bb0: %0 = "llvm.icmp"(%arg0, %arg1) : (!llvm.ptr, !llvm.ptr) -> i8: unsupported operand type !llvm.ptr -/
#guard_msgs in
mlir_def wrongResultWidth := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.PointerCompare

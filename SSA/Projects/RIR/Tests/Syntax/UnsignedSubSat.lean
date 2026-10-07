module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Run.Tactic
import all SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.Func

/-! Scalar unsigned saturating subtraction, including the i64 shape emitted by
the sha2 AVX2 loop. Underflow clamps to zero; neither operand's poison is masked.
https://llvm.org/docs/LangRef.html#llvm-usub-sat-intrinsics -/

namespace LeanMLIR.RIR.Tests.Syntax.UnsignedSubSat

@[expose] public section

mlir_def subtract64 := {
  ^bb0(%arg0: i64, %arg1: i64):
    %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (i64, i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

mlir_def subtract1 := {
  ^bb0(%arg0: i1, %arg1: i1):
    %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (i1, i1) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

mlir_def subtract128 := {
  ^bb0(%arg0: i128, %arg1: i128):
    %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (i128, i128) -> i128
    "llvm.return"(%0) : (i128) -> ()
}

-- `mlir_operation` exposes the exact unsigned comparison to the simplifier.
example {w : Nat} (a b : BitVec w) :
    Operation.usubSat (.value a) (.value b) =
      .value (if a.ult b then 0 else a - b) := by
  simp only [mlir_operation]

example {w : Nat} (a : BitVec w) :
    Operation.usubSat (.value a) .poison = .poison := by
  simp only [mlir_operation]

example {w : Nat} (b : PoisonOr (BitVec w)) :
    Operation.usubSat .poison b = .poison := by
  simp only [mlir_operation]

private def s0 : GlobalState := ⟨default, default⟩

private def result (f : Func) (args : Vals f.Γ.args) : PoisonOr (Option (Vals f.tRets)) :=
  Prod.fst <$> f.eval 1 args s0

-- The exact i64 instruction executes through the translator and denotation.
example : result subtract64 (subtract64.args (.value 3#64) (.value 5#64)) =
    .value (some (.cons (.value 0#64) .nil)) := rfl
example : result subtract64 (subtract64.args (.value 5#64) (.value 5#64)) =
    .value (some (.cons (.value 0#64) .nil)) := rfl
example : result subtract64 (subtract64.args (.value 9#64) (.value 5#64)) =
    .value (some (.cons (.value 4#64) .nil)) := rfl
example : result subtract64 (subtract64.args (.value 0#64) (.value 0#64)) =
    .value (some (.cons (.value 0#64) .nil)) := rfl
-- Values above the signed maximum remain unsigned, and subtraction never clamps up.
example : result subtract64
    (subtract64.args (.value 0xFFFFFFFFFFFFFFFF#64) (.value 1#64)) =
    .value (some (.cons (.value 0xFFFFFFFFFFFFFFFE#64) .nil)) := rfl
example : result subtract64
    (subtract64.args (.value 1#64) (.value 0xFFFFFFFFFFFFFFFF#64)) =
    .value (some (.cons (.value 0#64) .nil)) := rfl
example : result subtract64 (subtract64.args .poison (.value 0#64)) =
    .value (some (.cons .poison .nil)) := rfl
example : result subtract64 (subtract64.args (.value 0#64) .poison) =
    .value (some (.cons .poison .nil)) := rfl
example : result subtract64 (subtract64.args .poison .poison) =
    .value (some (.cons .poison .nil)) := rfl

-- Width polymorphism includes the smallest LLVM integer and widths above 64.
example : result subtract1 (subtract1.args (.value 0#1) (.value 1#1)) =
    .value (some (.cons (.value 0#1) .nil)) := rfl
example : result subtract1 (subtract1.args (.value 1#1) (.value 0#1)) =
    .value (some (.cons (.value 1#1) .nil)) := rfl
example : result subtract128
    (subtract128.args (.value 0x10000000000000000#128) (.value 1#128)) =
    .value (some (.cons (.value 0xFFFFFFFFFFFFFFFF#128) .nil)) := rfl

/-- error: ^bb0: %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (i64, i32) -> i64: the operand and result types must agree -/
#guard_msgs in
mlir_def mismatchedOperands := {
  ^bb0(%arg0: i64, %arg1: i32):
    %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (i64, i32) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/-- error: ^bb0: %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (i64, i64) -> i32: the operand and result types must agree -/
#guard_msgs in
mlir_def mismatchedResult := {
  ^bb0(%arg0: i64, %arg1: i64):
    %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (i64, i64) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

-- This extension deliberately admits only scalar source operations.
/-- error: ^bb0: %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (vector<2xi8>, vector<2xi8>) -> vector<2xi8>: expected two scalar integer operands -/
#guard_msgs in
mlir_def unsupportedVector := {
  ^bb0(%arg0: vector<2xi8>, %arg1: vector<2xi8>):
    %0 = "llvm.intr.usub.sat"(%arg0, %arg1) : (vector<2xi8>, vector<2xi8>) -> vector<2xi8>
    "llvm.return"(%0) : (vector<2xi8>) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.UnsignedSubSat

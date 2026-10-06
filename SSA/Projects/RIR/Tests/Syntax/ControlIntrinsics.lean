module

public import SSA.Projects.RIR.Syntax.Elab
import all SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.Func

/-! Tests of exact control and three-way comparison semantics. In particular, an
`assume` is an effectful UB check, never an unchecked proof premise or a no-op.

LLVM references:
https://llvm.org/docs/LangRef.html#llvm-assume-intrinsic
https://llvm.org/docs/LangRef.html#unreachable-instruction
https://llvm.org/docs/LangRef.html#llvm-scmp-intrinsic
-/

namespace LeanMLIR.RIR.Tests.Syntax.ControlIntrinsics

@[expose] public section

mlir_def assumed := {
  ^bb0(%arg0: i1, %arg1: i8):
    "llvm.intr.assume"(%arg0) <{op_bundle_sizes = array<i32>, op_bundle_tags = []}> : (i1) -> ()
    "llvm.return"(%arg1) : (i8) -> ()
}

mlir_def unreachableBranch := {
  ^bb0(%arg0: i1, %arg1: i8):
    "llvm.cond_br"(%arg0)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "llvm.return"(%arg1) : (i8) -> ()
  ^bb2:
    "llvm.unreachable"() : () -> ()
}

mlir_def signedCompare := {
  ^bb0(%arg0: i8, %arg1: i8):
    %0 = "llvm.intr.scmp"(%arg0, %arg1) : (i8, i8) -> i2
    "llvm.return"(%0) : (i2) -> ()
}

mlir_def unsignedCompare := {
  ^bb0(%arg0: i8, %arg1: i8):
    %0 = "llvm.intr.ucmp"(%arg0, %arg1) : (i8, i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

mlir_def vectorCompare := {
  ^bb0(%arg0: vector<2xi8>, %arg1: vector<2xi8>):
    %0 = "llvm.intr.scmp"(%arg0, %arg1) : (vector<2xi8>, vector<2xi8>) -> vector<2xi2>
    "llvm.return"(%0) : (vector<2xi2>) -> ()
}

-- Preserve both overflow promises in LLVM 22's numeric attribute spelling.
mlir_def numericOverflow := {
  ^bb0(%arg0: i8, %arg1: i8):
    %0 = "llvm.add"(%arg0, %arg1) <{overflowFlags = 0 : i32}> : (i8, i8) -> i8
    %1 = "llvm.add"(%arg0, %arg1) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %2 = "llvm.add"(%arg0, %arg1) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %3 = "llvm.add"(%arg0, %arg1) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    "llvm.return"(%0, %1, %2, %3) : (i8, i8, i8, i8) -> ()
}

-- These equalities quantify over arbitrary return poison and arbitrary memory.
example (v : PoisonOr (BitVec 8)) (s : GlobalState) :
    assumed.eval 1 (assumed.args (.value 1#1) v) s =
      .value (some (.cons v .nil), s) := rfl
example (v : PoisonOr (BitVec 8)) (s : GlobalState) :
    assumed.eval 1 (assumed.args (.value 0#1) v) s = .poison := rfl
example (v : PoisonOr (BitVec 8)) (s : GlobalState) :
    assumed.eval 1 (assumed.args .poison v) s = .poison := rfl
example (v : PoisonOr (BitVec 8)) (s : GlobalState) :
    unreachableBranch.eval 2 (unreachableBranch.args (.value 1#1) v) s =
      .value (some (.cons v .nil), s) := rfl
example (v : PoisonOr (BitVec 8)) (s : GlobalState) :
    unreachableBranch.eval 2 (unreachableBranch.args (.value 0#1) v) s = .poison := rfl

private def s0 : GlobalState := ⟨default, default⟩

private def result (f : Func) (args : Vals f.Γ.args) : PoisonOr (Option (Vals f.tRets)) :=
  Prod.fst <$> f.eval 2 args s0

example : result assumed (assumed.args (.value 1#1) (.value 7#8)) =
  .value (some (.cons (.value 7#8) .nil)) := rfl
example : result assumed (assumed.args (.value 0#1) (.value 7#8)) = .poison := rfl
example : result assumed (assumed.args .poison (.value 7#8)) = .poison := rfl
-- A poison return value alone is not immediate UB.
example : result assumed (assumed.args (.value 1#1) .poison) =
  .value (some (.cons .poison .nil)) := rfl
example : result unreachableBranch (unreachableBranch.args (.value 1#1) (.value 7#8)) =
  .value (some (.cons (.value 7#8) .nil)) := rfl
example : result unreachableBranch (unreachableBranch.args (.value 0#1) (.value 7#8)) = .poison := rfl
example : result unreachableBranch (unreachableBranch.args .poison (.value 7#8)) = .poison := rfl
example : result signedCompare (signedCompare.args (.value 255#8) (.value 0#8)) =
  .value (some (.cons (.value 3#2) .nil)) := rfl
example : result signedCompare (signedCompare.args (.value 0#8) (.value 0#8)) =
  .value (some (.cons (.value 0#2) .nil)) := rfl
example : result signedCompare (signedCompare.args (.value 127#8) (.value 128#8)) =
  .value (some (.cons (.value 1#2) .nil)) := rfl
example : result unsignedCompare (unsignedCompare.args (.value 255#8) (.value 0#8)) =
  .value (some (.cons (.value 1#8) .nil)) := rfl
example : result unsignedCompare (unsignedCompare.args (.value 0#8) (.value 255#8)) =
  .value (some (.cons (.value 255#8) .nil)) := rfl
example : result signedCompare (signedCompare.args .poison (.value 0#8)) =
  .value (some (.cons .poison .nil)) := rfl
private def vectorResult : Option (Vector (PoisonOr (BitVec 2)) 2) :=
  match vectorCompare.eval 1
      (vectorCompare.args #v[.value 255#8, .poison] #v[.value 0#8, .value 0#8]) s0 with
  | .value (some (.cons v .nil), _) => some v
  | _ => none
#guard vectorResult == some #v[.value 3#2, .poison]

example : result numericOverflow (numericOverflow.args (.value 127#8) (.value 1#8)) =
  .value (some (.cons (.value 128#8) (.cons .poison (.cons (.value 128#8) (.cons .poison .nil))))) := rfl
example : result numericOverflow (numericOverflow.args (.value 255#8) (.value 1#8)) =
  .value (some (.cons (.value 0#8) (.cons (.value 0#8) (.cons .poison (.cons .poison .nil))))) := rfl

/-- error: ^bb0: %0 = "llvm.add"(%arg0, %arg1) : (i8, i8) -> i8: unknown overflow flag bits `4` -/
#guard_msgs in
mlir_def invalidOverflow := {
  ^bb0(%arg0: i8, %arg1: i8):
    %0 = "llvm.add"(%arg0, %arg1) <{overflowFlags = 4 : i32}> : (i8, i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/-- error: ^bb0: "llvm.intr.assume"(%arg0) : (i1) -> (): assume operand bundles are not supported -/
#guard_msgs in
mlir_def unsupportedBundle := {
  ^bb0(%arg0: i1):
    "llvm.intr.assume"(%arg0) <{op_bundle_sizes = array<i32: 0>, op_bundle_tags = ["cold"]}> : (i1) -> ()
    "llvm.return"() : () -> ()
}

/-- error: ^bb0: %0 = "llvm.freeze"(%arg0) : (i8) -> i8: freeze requires nondeterministic semantics and is not supported -/
#guard_msgs in
mlir_def unsupportedFreeze := {
  ^bb0(%arg0: i8):
    %0 = "llvm.freeze"(%arg0) : (i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/-- error: ^bb0: %0 = "llvm.intr.scmp"(%arg0, %arg1) : (i8, i8) -> i1: three-way comparison requires at least two result bits -/
#guard_msgs in
mlir_def narrowCompare := {
  ^bb0(%arg0: i8, %arg1: i8):
    %0 = "llvm.intr.scmp"(%arg0, %arg1) : (i8, i8) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.ControlIntrinsics

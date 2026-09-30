module

public import SSA.Projects.RIR.Syntax.Elab

/-! # `mlir_def`: errors name the operation, its types and what is wrong -/

namespace LeanMLIR.RIR.Tests.Syntax.Errors

/-- error: ^bb0: %1 = "llvm.add"(%arg0, %0) : (i32, i32) -> i32: %0 has type i64 but is used at i32 -/
#guard_msgs in
mlir_def typeMismatch := {
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.add"(%arg0, %0) : (i32, i32) -> i32
    "llvm.return"(%1) : (i32) -> ()
}

/--
error: ^bb0: %0 = "llvm.add"(%arg0, %arg1) : (i32, i64) -> i32: the operand and result types must agree
-/
#guard_msgs in
mlir_def opTypeMismatch := {
  ^bb0(%arg0: i32, %arg1: i64):
    %0 = "llvm.add"(%arg0, %arg1) : (i32, i64) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

/-- error: ^bb0: "llvm.br"()[^bb1] : () -> (): ^bb1 takes 1 argument(s), but the jump passes 0 -/
#guard_msgs in
mlir_def jumpArity := {
  ^bb0(%arg0: i32):
    "llvm.br"()[^bb1] : () -> ()
  ^bb1(%0: i32):
    "llvm.return"(%0) : (i32) -> ()
}

/--
error: ^bb0: "llvm.br"(%arg0)[^bb1] : (i64) -> (): argument 0 of the jump to ^bb1 has type i64, expected i32
-/
#guard_msgs in
mlir_def jumpType := {
  ^bb0(%arg0: i64):
    "llvm.br"(%arg0)[^bb1] : (i64) -> ()
  ^bb1(%0: i32):
    "llvm.return"(%0) : (i32) -> ()
}

/-- error: ^bb0: "llvm.br"()[^bb7] : () -> (): unknown block ^bb7 -/
#guard_msgs in
mlir_def unknownBlock := {
  ^bb0(%arg0: i32):
    "llvm.br"()[^bb7] : () -> ()
}

/-- error: ^bb0: "llvm.return"(%3) : (i32) -> (): %3 is not defined -/
#guard_msgs in
mlir_def unknownValue := {
  ^bb0(%arg0: i32):
    "llvm.return"(%3) : (i32) -> ()
}

/-- error: ^bb0: "llvm.return"(%arg1) : (i32) -> (): %arg1 is not an argument of the function -/
#guard_msgs in
mlir_def argOutOfRange := {
  ^bb0(%arg0: i32):
    "llvm.return"(%arg1) : (i32) -> ()
}

/-- error: %0 is defined twice -/
#guard_msgs in
mlir_def definedTwice := {
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %0 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    "llvm.return"(%0) : (i32) -> ()
}

/-- error: ^bb0: %0 = "llvm.udiv"(%arg0, %arg1) : (i32, i32) -> i32: unsupported operation 'llvm.udiv' -/
#guard_msgs in
mlir_def unsupportedOp := {
  ^bb0(%arg0: i32, %arg1: i32):
    %0 = "llvm.udiv"(%arg0, %arg1) : (i32, i32) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

/-- error: unsupported MLIR type 'f32' -/
#guard_msgs in
mlir_def unsupportedType := {
  ^bb0(%arg0: f32):
    "llvm.return"(%arg0) : (f32) -> ()
}

/-- error: %arg0: unsupported type !llvm.struct<(i64, i64)> -/
#guard_msgs in
mlir_def unsupportedStruct := {
  ^bb0(%arg0: !llvm.struct<(i64, i64)>):
    "llvm.return"() : () -> ()
}

/-- error: ^bb0: %1 = "llvm.alloca"(%0) : (i32) -> !llvm.ptr: the count %0 must be the constant 1 -/
#guard_msgs in
mlir_def allocaCount := {
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    "llvm.return"() : () -> ()
}

/-- error: ^bb0: %0 = "llvm.load"(%arg0) : (!llvm.ptr) -> i64: atomic accesses are not supported -/
#guard_msgs in
mlir_def atomic := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.load"(%arg0) <{ordering = 2 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/-- error: ^bb0: %0 = "llvm.icmp"(%arg0, %arg1) : (i64, i64) -> i1: unknown predicate 10 -/
#guard_msgs in
mlir_def predicate := {
  ^bb0(%arg0: i64, %arg1: i64):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 10 : i64}> : (i64, i64) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

/-- error: llvm.call to @g: no callee bound; add `with @g := …`, or define a `g : Func` -/
#guard_msgs in
mlir_def noCallee := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/--
error: @g: the call sites need a callee of type
  Vals [Ty.bv 64] → EffectM (Vals [Ty.bv 64])
but the term has type
  Vals [Ty.bv 32] → EffectM (Vals [Ty.bv 32])
-/
#guard_msgs in
mlir_def calleeType (g : Vals [.bv 32] → EffectM (Vals [.bv 32])) := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
} with @g := g

/--
error: ^bb0: %0 = "llvm.add"(%arg0, %arg0) : (i64, i64) -> i64: 'llvm.add' is not a terminator; a block must end in llvm.return, llvm.br, llvm.cond_br or llvm.switch
-/
#guard_msgs in
mlir_def notTerminated := {
  ^bb0(%arg0: i64):
    %0 = "llvm.add"(%arg0, %arg0) : (i64, i64) -> i64
}

/--
error: ^bb0: %0 = "llvm.getelementptr"(%arg0, %arg1) : (!llvm.ptr, i64) -> !llvm.ptr: only constant indices are supported
-/
#guard_msgs in
mlir_def gepDynamic := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

/-- error: ^bb2: "llvm.return"() : () -> (): returns (), but another llvm.return returns (i64) -/
#guard_msgs in
mlir_def returnTypes := {
  ^bb0(%arg0: i64, %arg1: i1):
    "llvm.cond_br"(%arg1)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "llvm.return"(%arg0) : (i64) -> ()
  ^bb2:
    "llvm.return"() : () -> ()
}

/--
error: ^bb0: %0 = "llvm.shufflevector"(%arg0, %arg0) : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>: the mask has 2 lanes, expected 4
-/
#guard_msgs in
mlir_def shuffleMask := {
  ^bb0(%arg0: vector<4xi32>):
    %0 = "llvm.shufflevector"(%arg0, %arg0) <{mask = array<i32: 0, 1>}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    "llvm.return"(%0) : (vector<4xi32>) -> ()
}

/-- error: ^bb0: "llvm.return"(%arg0) : (i32) -> (): a terminator must end its block -/
#guard_msgs in
mlir_def midTerminator := {
  ^bb0(%arg0: i32):
    "llvm.return"(%arg0) : (i32) -> ()
    "llvm.return"(%arg0) : (i32) -> ()
}

-- `sext` translates, and only widens
#guard_msgs in
mlir_def sextWiden := {
  ^bb0(%arg0: i1):
    %0 = "llvm.sext"(%arg0) : (i1) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

example : sextWiden.entry.body = [.unop (.sext (w := 1) (w' := 8)) ⟨0, rfl⟩ (.arg 0 rfl)] := rfl

/-- error: ^bb0: %0 = "llvm.sext"(%arg0) : (i32) -> i8: the result must be wider -/
#guard_msgs in
mlir_def sextNarrow := {
  ^bb0(%arg0: i32):
    %0 = "llvm.sext"(%arg0) : (i32) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

-- `shufflevector` may change the lane count, as `fd_r43x6_unpack` widens `4 x i64` to `8 x i64`
#guard_msgs in
mlir_def shuffleWiden := {
  ^bb0(%arg0: vector<2xi64>, %arg1: vector<2xi64>):
    %0 = "llvm.shufflevector"(%arg0, %arg1) <{mask = array<i32: 0, 1, 2, 3, -1>}> : (vector<2xi64>, vector<2xi64>) -> vector<5xi64>
    "llvm.return"(%0) : (vector<5xi64>) -> ()
}

/--
error: ^bb0: %0 = "llvm.shufflevector"(%arg0, %arg1) : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>: mask index 4 out of range
-/
#guard_msgs in
mlir_def shuffleRange := {
  ^bb0(%arg0: vector<2xi64>, %arg1: vector<2xi64>):
    %0 = "llvm.shufflevector"(%arg0, %arg1) <{mask = array<i32: 0, 4>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.return"(%0) : (vector<2xi64>) -> ()
}

/--
error: ^bb0: %0 = "llvm.shufflevector"(%arg0, %arg1) : (vector<2xi64>, vector<2xi64>) -> vector<2xi32>: the input and output element widths must agree
-/
#guard_msgs in
mlir_def shuffleWidth := {
  ^bb0(%arg0: vector<2xi64>, %arg1: vector<2xi64>):
    %0 = "llvm.shufflevector"(%arg0, %arg1) <{mask = array<i32: 0, 1>}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi32>
    "llvm.return"(%0) : (vector<2xi32>) -> ()
}

-- a vector condition selects lane-wise
#guard_msgs in
mlir_def vectorSelect := {
  ^bb0(%arg0: vector<4xi1>, %arg1: vector<4xi32>):
    %0 = "llvm.select"(%arg0, %arg1, %arg1) : (vector<4xi1>, vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    "llvm.return"(%0) : (vector<4xi32>) -> ()
}

example :
    vectorSelect.entry.body =
      [.ternop (.vector (l := 4) (.select (τ := .bv 32))) ⟨0, rfl⟩ (.arg 0 rfl) (.arg 1 rfl)
        (.arg 1 rfl)] := rfl

/--
error: ^bb0: %0 = "llvm.select"(%arg0, %arg1, %arg1) : (vector<2xi1>, vector<4xi32>, vector<4xi32>) -> vector<4xi32>: vector condition has wrong lane count
-/
#guard_msgs in
mlir_def vectorSelectLanes := {
  ^bb0(%arg0: vector<2xi1>, %arg1: vector<4xi32>):
    %0 = "llvm.select"(%arg0, %arg1, %arg1) : (vector<2xi1>, vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    "llvm.return"(%0) : (vector<4xi32>) -> ()
}

-- `undef` translates, as poison
#guard_msgs in
mlir_def undef := {
  ^bb0(%arg0: i32):
    %0 = "llvm.mlir.undef"() : () -> i32
    "llvm.return"(%0) : (i32) -> ()
}

end LeanMLIR.RIR.Tests.Syntax.Errors

module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func

/-! # `mlir_def`: errors name the operation, its types and what is wrong -/

namespace MLIR.Tests.Syntax.Errors

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

/--
error: ^bb0: %0 = "llvm.extractvalue"(%arg0) : (!llvm.array<2 x vector<4xi8>>) -> i8: the position must not index into a vector
-/
#guard_msgs in
mlir_def extractLane := {
  ^bb0(%arg0: !llvm.array<2 x vector<4xi8>>):
    %0 = "llvm.extractvalue"(%arg0) <{position = array<i64: 1, 3>}> : (!llvm.array<2 x vector<4xi8>>) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/-- error: unsupported MLIR type 'f32' -/
#guard_msgs in
mlir_def unsupportedType := {
  ^bb0(%arg0: f32):
    "llvm.return"(%arg0) : (f32) -> ()
}

/-- error: %arg0: cannot decode the type !llvm.struct<(i64, f32)> -/
#guard_msgs in
mlir_def unsupportedStruct := {
  ^bb0(%arg0: !llvm.struct<(i64, f32)>):
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

/-- error: ^bb0: %0 = "llvm.load"(%arg0) : (!llvm.ptr) -> i64: unknown atomic ordering 3 -/
#guard_msgs in
mlir_def atomic := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.load"(%arg0) <{ordering = 3 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/-- error: ^bb0: %0 = "llvm.icmp"(%arg0, %arg1) : (i64, i64) -> i1: unknown predicate 10 -/
#guard_msgs in
mlir_def predicate := {
  ^bb0(%arg0: i64, %arg1: i64):
    %0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 10 : i64}> : (i64, i64) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

/-- error: llvm.call to @g: no callee bound; add `with @g := …` -/
#guard_msgs in
mlir_def noCallee := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

mlir_def id32 := {
  ^bb0(%arg0: i32):
    "llvm.return"(%arg0) : (i32) -> ()
}

mlir_def id64 := {
  ^bb0(%arg0: i64):
    "llvm.return"(%arg0) : (i64) -> ()
}

/--
error: @g: the call sites need a callee of type
  Vals [Ty.bv 64] → EffectM (Vals [Ty.bv 64])
but `id32.call` has type
  Vals [Ty.bv 32] → EffectM (Vals [Ty.bv 32])
-/
#guard_msgs in
mlir_def calleeType := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
} with @g := id32

-- a function of the call's type, not a `Func`: called as given
/-- warning: @g is bound to a function, not a `Func`: the calls run it as given, not a lifted region -/
#guard_msgs in
mlir_def calleeFn (g : Vals [.bv 64] → EffectM (Vals [.bv 64])) := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
} with @g := g

/-- `x + 1`, as `@g`. -/
def succ64 (v : Vals [.bv 64]) : EffectM (Vals [.bv 64]) :=
  match v with
  | .cons x .nil => pure (.cons ((· + 1) <$> x) .nil)

#guard (match (calleeFn succ64).eval 1 (calleeFn.args (.value 41)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none) == some 42

/--
error: @g: expected a `Func`, or a function of type
  Vals [Ty.bv 64] → EffectM (Vals [Ty.bv 64])
but `g` has type
  Vals [Ty.bv 32] → EffectM (Vals [Ty.bv 32])
-/
#guard_msgs in
mlir_def calleeFnType (g : Vals [.bv 32] → EffectM (Vals [.bv 32])) := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
} with @g := g

/-- `id64`, for any `k`. -/
def pick (_ : Nat) : Func := id64

-- a single block whose callee mentions a binder: `blocks` applies it
#guard_msgs in
mlir_def calleeBinder (k : Nat) := {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
} with @g := pick k

example (k : Nat) : (calleeBinder k).blocks 0 = calleeBinder.entry k := rfl

/--
error: ^bb0: %0 = "llvm.add"(%arg0, %arg0) : (i64, i64) -> i64: 'llvm.add' is not a terminator; a block must end in llvm.return, llvm.unreachable, llvm.br, llvm.cond_br or llvm.switch
-/
#guard_msgs in
mlir_def notTerminated := {
  ^bb0(%arg0: i64):
    %0 = "llvm.add"(%arg0, %arg0) : (i64, i64) -> i64
}

/--
error: ^bb0: %0 = "llvm.getelementptr"(%arg0, %arg1) : (!llvm.ptr, i64) -> !llvm.ptr: a dynamic index must index an array
-/
#guard_msgs in
mlir_def gepDynamicField := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = !llvm.struct<(i64, i64)>, rawConstantIndices = array<i32: 0, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
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

/--
error: ^bb0: "llvm.intr.assume"(%arg0, %arg1) : (i1, !llvm.ptr) -> (): operand bundles are not supported
-/
#guard_msgs in
mlir_def assumeBundle := {
  ^bb0(%arg0: i1, %arg1: !llvm.ptr):
    "llvm.intr.assume"(%arg0, %arg1) <{op_bundle_sizes = array<i32: 1>, op_bundle_tags = ["nonnull"]}> : (i1, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

/-! ## Fail-closed imports of newer ops -/

/--
error: ^bb0: %0 = "llvm.inline_asm"(%arg0) : (i8) -> i8: only an empty asm returning its operand is supported
-/
#guard_msgs in
mlir_def asmText := {
  ^bb0(%arg0: i8):
    %0 = "llvm.inline_asm"(%arg0) <{asm_dialect = 0 : i64, asm_string = "nop", constraints = "=r,0", tail_call_kind = #llvm.tailcallkind<tail>}> : (i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/-- error: ^bb0: %0 = "llvm.inline_asm"(%arg0) : (i8) -> i8: unsupported constraints "=r,r" -/
#guard_msgs in
mlir_def asmUntied := {
  ^bb0(%arg0: i8):
    %0 = "llvm.inline_asm"(%arg0) <{asm_dialect = 0 : i64, asm_string = "", constraints = "=r,r"}> : (i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/--
error: ^bb0: %0 = "llvm.inline_asm"(%arg0) : (i8) -> i8: unsupported constraints "=r,0,~{rbx}"
-/
#guard_msgs in
mlir_def asmClobber := {
  ^bb0(%arg0: i8):
    %0 = "llvm.inline_asm"(%arg0) <{asm_dialect = 0 : i64, asm_string = "", constraints = "=r,0,~{rbx}"}> : (i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/--
error: ^bb0: %0 = "llvm.cmpxchg"(%arg0, %arg1, %arg1) : (!llvm.ptr, i64, i64) -> !llvm.struct<(i64, i1)>: unsupported attribute `failure_ordering`
-/
#guard_msgs in
mlir_def cmpxchg := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.cmpxchg"(%arg0, %arg1, %arg1) <{failure_ordering = 2 : i64, success_ordering = 2 : i64}> : (!llvm.ptr, i64, i64) -> !llvm.struct<(i64, i1)>
    "llvm.return"() : () -> ()
}

/--
error: ^bb0: %0 = "llvm.atomicrmw"(%arg0, %arg1) : (!llvm.ptr, i64) -> i64: unsupported attribute `bin_op`
-/
#guard_msgs in
mlir_def atomicrmw := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.atomicrmw"(%arg0, %arg1) <{bin_op = 1 : i64, ordering = 2 : i64}> : (!llvm.ptr, i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/-- error: ^bb0: %0 = "llvm.inttoptr"(%arg0) : (i64) -> !llvm.ptr: unsupported operation 'llvm.inttoptr' -/
#guard_msgs in
mlir_def inttoptr := {
  ^bb0(%arg0: i64):
    %0 = "llvm.inttoptr"(%arg0) : (i64) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

/-- error: ^bb0: %0 = "llvm.ptrtoaddr"(%arg0) : (!llvm.ptr) -> i32: expected an `i64` result -/
#guard_msgs in
mlir_def ptrtoaddrWidth := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.ptrtoaddr"(%arg0) : (!llvm.ptr) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

/--
error: ^bb0: %0 = "llvm.intr.scmp"(%arg0, %arg0) : (i8, i8) -> i1: expected two operands of one type, and a result of at least 2 bits
-/
#guard_msgs in
mlir_def scmpBit := {
  ^bb0(%arg0: i8):
    %0 = "llvm.intr.scmp"(%arg0, %arg0) : (i8, i8) -> i1
    "llvm.return"(%0) : (i1) -> ()
}

/--
error: ^bb0: %0 = "llvm.intr.bswap"(%arg0) : (i8) -> i8: expected a result of the operand's type, an even number of bytes
-/
#guard_msgs in
mlir_def bswapByte := {
  ^bb0(%arg0: i8):
    %0 = "llvm.intr.bswap"(%arg0) : (i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/-- error: %arg0: cannot decode the type !llvm.struct<packed (i8, i64)> -/
#guard_msgs in
mlir_def packedPadded := {
  ^bb0(%arg0: !llvm.struct<packed (i8, i64)>):
    "llvm.return"() : () -> ()
}

/-- error: @bcmp does not have the type the call site needs -/
#guard_msgs in
mlir_def bcmpType := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i32):
    %0 = "llvm.call"(%arg0, %arg0, %arg1) <{callee = @bcmp, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i32) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

/-- error: llvm.call to @strlen: no callee bound; add `with @strlen := …` -/
#guard_msgs in
mlir_def unknownExternal := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.call"(%arg0) <{callee = @strlen, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/-- error: ^bb0: "llvm.store"(%arg1, %arg0) : (i64, !llvm.ptr) -> (): unsupported attribute `nontemporal` -/
#guard_msgs in
mlir_def nontemporal := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    "llvm.store"(%arg1, %arg0) <{alignment = 8 : i64, nontemporal, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

end MLIR.Tests.Syntax.Errors

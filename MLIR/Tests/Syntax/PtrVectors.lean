module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # Pointer vectors, `vector<n x !llvm.ptr>` as `.array n .ptr`: `getelementptr` lane-wise,
`load` and `store` as an array's -/

namespace MLIR.Tests.Syntax.PtrVectors

@[expose] public section

/-- Four pointers into `%arg0`'s block stored at `%arg1`, loaded back, each a word on. -/
mlir_def spread := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[0, 8, 16, 24]> : vector<4xi64>}> : () -> vector<4xi64>
    %1 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, vector<4xi64>) -> vector<4x!llvm.ptr>
    "llvm.store"(%1, %arg1) <{alignment = 16 : i64, ordering = 0 : i64}> : (vector<4x!llvm.ptr>, !llvm.ptr) -> ()
    %2 = "llvm.load"(%arg1) <{alignment = 16 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<4x!llvm.ptr>
    %3 = "llvm.getelementptr"(%2) <{elem_type = i64, rawConstantIndices = array<i32: 1>}> : (vector<4x!llvm.ptr>) -> vector<4x!llvm.ptr>
    "llvm.return"(%3) : (vector<4x!llvm.ptr>) -> ()
}

/-- A pointer vector stepped by one scalar index. -/
mlir_def bump := {
  ^bb0(%arg0: vector<2x!llvm.ptr>, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i32, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (vector<2x!llvm.ptr>, i64) -> vector<2x!llvm.ptr>
    "llvm.return"(%0) : (vector<2x!llvm.ptr>) -> ()
}

/-- One pointer stepped by a vector of indices. -/
mlir_def splay := {
  ^bb0(%arg0: !llvm.ptr, %arg1: vector<4xi64>):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i8, noWrapFlags = 0 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, vector<4xi64>) -> vector<4x!llvm.ptr>
    "llvm.return"(%0) : (vector<4x!llvm.ptr>) -> ()
}

end

/-- error: ^bb0: %1 = "llvm.extractelement"(%arg0, %0) : (vector<2x!llvm.ptr>, i64) -> !llvm.ptr: pointer vectors are supported only by llvm.getelementptr, llvm.load, llvm.store, llvm.mlir.poison, llvm.mlir.undef, llvm.mlir.zero, llvm.call -/
#guard_msgs in
mlir_def lane := {
  ^bb0(%arg0: vector<2x!llvm.ptr>):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %1 = "llvm.extractelement"(%arg0, %0) : (vector<2x!llvm.ptr>, i64) -> !llvm.ptr
    "llvm.return"(%1) : (!llvm.ptr) -> ()
}

/-! ## Execution tests -/

section Tests

/-- Blocks `1` and `2`, 32 bytes each. -/
private def s0 : GlobalState :=
  ⟨⟨3⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 32 0), (⟨2⟩, .ofBytes 32 0)]⟩⟩

private def ptrs (os : List Nat) : List (PoisonOr Pointer) :=
  os.map fun o => .value ⟨⟨1⟩, BitVec.ofNat 64 o⟩

-- stored as four pointers and loaded back
#guard (match spread.eval 1 (spread.args (.value ⟨⟨1⟩, 0⟩) (.value ⟨⟨2⟩, 0⟩)) s0 with
  | .value (some (.cons v .nil), _) => v.toList == ptrs [8, 16, 24, 32]
  | _ => false)

-- `inbounds`: a lane leaving its block below is poison, alone
#guard (match bump.eval 1 (bump.args #v[.value ⟨⟨1⟩, 4⟩, .value ⟨⟨1⟩, 0⟩] (.value (-1))) s0 with
  | .value (some (.cons v .nil), _) => v.toList == [.value ⟨⟨1⟩, 0⟩, .poison]
  | _ => false)

#guard (match splay.eval 1 (splay.args (.value ⟨⟨1⟩, 0⟩) #v[.value 3, .poison, .value 0, .value 1])
    s0 with
  | .value (some (.cons v .nil), _) => v.toList == [.value ⟨⟨1⟩, 3⟩, .poison, .value ⟨⟨1⟩, 0⟩,
    .value ⟨⟨1⟩, 1⟩]
  | _ => false)

end Tests

/-! ## Steps -/

section Steps

-- `step_pure`: lane `k` the scalar `gepDyn`'s
example (p : Pointer) (i : ⟦Ty.vec 4 64⟧) (s : GlobalState) (hwf : s.WF) :
    splay.call (splay.args (.value p) i) s =
      .value (.cons (Vector.ofFn fun k => Operation.gepDyn {} 0 1 (.value p) i[k]) .nil, s) := by
  func_init
  block_init
  step_pure with r
  finish_block
  subst_vars
  rfl

end Steps

end MLIR.Tests.Syntax.PtrVectors

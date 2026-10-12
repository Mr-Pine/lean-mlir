module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func

/-! # `llvm.getelementptr` with a dynamic index, or a negative constant one -/

namespace MLIR.Tests.Syntax.Gep

@[expose] public section

mlir_def loadAt := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
}

mlir_def loadAtNuw := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
}

mlir_def loadAtInbounds := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, noWrapFlags = 3 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
}

mlir_def loadField := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = !llvm.struct<(i64, array<4 x i16>)>, rawConstantIndices = array<i32: 0, 1, -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 2 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i16
    "llvm.return"(%1) : (i16) -> ()
}

mlir_def loadBack := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.getelementptr"(%arg0) <{elem_type = i64, rawConstantIndices = array<i32: -1>}> : (!llvm.ptr) -> !llvm.ptr
    %1 = "llvm.load"(%0) <{alignment = 8 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%1) : (i64) -> ()
}

end

/-! ## Execution tests -/

section Tests

private def p : Pointer := ⟨⟨1⟩, 0⟩

/-- Block `1`: the `i64`s `10, 20, 30, 40, 50`, lowest first. -/
private def limbs : GlobalState :=
  ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 40 (50#64 ++ 40#64 ++ 30#64 ++ 20#64 ++ 10#64))]⟩⟩

/-- `loadAt`'s `i64` at index `i`, or `none` for UB. -/
private def at_ (i : BitVec 64) : Option (BitVec 64) :=
  match loadAt.eval 1 (loadAt.args (.value p) (.value i)) limbs with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard (List.range 5).map (fun i => at_ (BitVec.ofNat 64 i)) == [10, 20, 30, 40, 50].map some
-- past the block: no load
#guard at_ 5 == none
-- no flags: `2 ^ 61 * 8` wraps to the start
#guard at_ (BitVec.ofNat 64 (2 ^ 61)) == some 10

/-- `at_` with `inbounds nuw` (`nuw`), or `inbounds` alone (not `nuw`), from byte `off`. -/
private def atFlags (nuw : Bool) (off i : BitVec 64) : Option (BitVec 64) :=
  let s := if nuw then loadAtNuw.eval 1 (loadAtNuw.args (.value ⟨⟨1⟩, off⟩) (.value i)) limbs
    else loadAtInbounds.eval 1 (loadAtInbounds.args (.value ⟨⟨1⟩, off⟩) (.value i)) limbs
  match s with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard atFlags true 0 2 == some 30
-- the offset wraps: a poison pointer
#guard atFlags true 0 (BitVec.ofNat 64 (2 ^ 61)) == none
#guard atFlags false 0 (BitVec.ofNat 64 (2 ^ 61)) == none
-- index `-1`, signed for `inbounds`, unsigned (wrapping) for `nuw`
#guard atFlags false 16 (-1) == some 20
#guard atFlags true 16 (-1) == none
-- before the block's start
#guard atFlags false 0 (-1) == none

/-- Block `1`: the `struct<(i64, array<4 x i16>)>` `(7, [1, 2, 3, 4])`. -/
private def record : GlobalState :=
  ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 16 (4#16 ++ 3#16 ++ 2#16 ++ 1#16 ++ 7#64))]⟩⟩

/-- `loadField`'s `i16` at index `i` of the array field, or `none` for UB. -/
private def field (i : BitVec 64) : Option (BitVec 16) :=
  match loadField.eval 1 (loadField.args (.value p) (.value i)) record with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard (List.range 4).map (fun i => field (BitVec.ofNat 64 i)) == [1, 2, 3, 4].map some

/-- `loadBack`'s `i64` before byte `off` of block `1`, or `none` for UB. -/
private def back (off : BitVec 64) : Option (BitVec 64) :=
  match loadBack.eval 1 (loadBack.args (.value ⟨⟨1⟩, off⟩)) limbs with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard back 8 == some 10
#guard back 40 == some 50
-- before the block's start: a poison pointer
#guard back 0 == none

end Tests

end MLIR.Tests.Syntax.Gep

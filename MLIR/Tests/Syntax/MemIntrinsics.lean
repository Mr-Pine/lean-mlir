module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func

/-! # `mlir_def` on `llvm.intr.memset` and `llvm.intr.memcpy` -/

namespace MLIR.Tests.Syntax.MemIntrinsics

@[expose] public section

mlir_def fill := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i8, %arg2: i64):
    "llvm.intr.memset"(%arg0, %arg1, %arg2) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
}

mlir_def copy := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i32):
    "llvm.intr.memcpy"(%arg0, %arg1, %arg2) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i32) -> ()
    "llvm.return"() : () -> ()
}

example : fill.entry.body = [.memset (.arg 0 rfl) (.arg 1 rfl) (.arg 2 rfl)] := rfl
example : copy.entry.body = [.memcpy (.arg 0 rfl) (.arg 1 rfl) (.arg 2 rfl)] := rfl

end

/-! ## Execution tests -/

section Tests

private def dst : Pointer := ⟨⟨0⟩, 0⟩
private def src : Pointer := ⟨⟨1⟩, 0⟩

/-- `dst` zeroed, `src` holding `0xAABBCCDD`, both 4 bytes. -/
private def s0 : GlobalState :=
  ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, .ofBytes 4 0), (⟨1⟩, .ofBytes 4 0xAABBCCDD#32)]⟩⟩

/-- `dst`'s bytes after the run, or `none` for UB. -/
private def fillOut (v : BitVec 8) (n : Nat) : Option (BitVec 32) :=
  match fill.eval 1 (fill.args (.value dst) (.value v) (.value (BitVec.ofNat 64 n))) s0 with
  | .value (some _, s) => some (s.mem.readAt dst 32)
  | _ => none

private def copyOut (d : Pointer) (n : Nat) : Option (BitVec 32) :=
  match copy.eval 1 (copy.args (.value d) (.value src) (.value (BitVec.ofNat 32 n))) s0 with
  | .value (some _, s) => some (s.mem.readAt d 32)
  | _ => none

#guard fillOut 0x7F 3 == some 0x007F7F7F#32
#guard fillOut 0x7F 5 == none
#guard copyOut dst 2 == some 0x0000CCDD#32
#guard copyOut dst 4 == some 0xAABBCCDD#32
#guard copyOut dst 5 == none
-- overlapping: `src` into itself, one byte on
#guard copyOut ⟨⟨1⟩, 1⟩ 2 == none

end Tests

end MLIR.Tests.Syntax.MemIntrinsics

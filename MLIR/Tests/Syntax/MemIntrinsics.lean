module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `mlir_def` on `llvm.intr.memset`, `llvm.intr.memcpy` and `llvm.intr.memmove` -/

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

/-- A `memmove`, volatile: a plain one. -/
mlir_def move := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    "llvm.intr.memmove"(%arg0, %arg1, %arg2) <{arg_attrs = [{llvm.align = 1 : i64}, {llvm.align = 1 : i64}, {}], isVolatile = true}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
}

example : fill.entry.body = [.memset (.arg 0 rfl) (.arg 1 rfl) (.arg 2 rfl)] := rfl
example : copy.entry.body = [.memcpy (.arg 0 rfl) (.arg 1 rfl) (.arg 2 rfl)] := rfl
example : move.entry.body = [.memmove (.arg 0 rfl) (.arg 1 rfl) (.arg 2 rfl)] := rfl

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

/-- The 4-byte blocks `dst` and `src` after the run, or `none` for UB. -/
private def moveOut (d : Pointer) (n : Nat) : Option (BitVec 32 × BitVec 32) :=
  match move.eval 1 (move.args (.value d) (.value src) (.value (BitVec.ofNat 64 n))) s0 with
  | .value (some _, s) => some (s.mem.readAt dst 32, s.mem.readAt src 32)
  | _ => none

#guard moveOut dst 4 == some (0xAABBCCDD#32, 0xAABBCCDD#32)
#guard moveOut dst 5 == none
-- overlapping: `src` into itself, one byte on, read before it is written
#guard moveOut ⟨⟨1⟩, 1⟩ 2 == some (0, 0xAACCDDDD#32)
#guard moveOut ⟨⟨1⟩, 1⟩ 3 == some (0, 0xBBCCDDDD#32)

end Tests

/-! ## Steps -/

section Steps

-- `step_memmove`: the ranges may overlap
example (q p : Pointer) (s : GlobalState) (hwf : s.WF) (hq : Room s.mem q 32)
    (hp : Fits s.mem p 32) :
    move.call (move.args (.value q) (.value p) (.value 4)) s =
      .value (.nil, { s with mem := s.mem.storeAt q (s.mem.readAt p 32) }) := by
  func_init
  block_init
  step_memmove
  finish_block
  rw [hS]

end Steps

end MLIR.Tests.Syntax.MemIntrinsics

module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `llvm.intr.masked.load` and `llvm.intr.masked.store`: only the lanes the mask sets access
memory -/

namespace MLIR.Tests.Syntax.Masked

@[expose] public section

mlir_def mload := {
  ^bb0(%arg0: !llvm.ptr, %arg1: vector<4xi1>, %arg2: vector<4xi32>):
    %0 = "llvm.intr.masked.load"(%arg0, %arg1, %arg2) <{alignment = 4 : i32}> : (!llvm.ptr, vector<4xi1>, vector<4xi32>) -> vector<4xi32>
    "llvm.return"(%0) : (vector<4xi32>) -> ()
}

mlir_def mstore := {
  ^bb0(%arg0: vector<4xi32>, %arg1: !llvm.ptr, %arg2: vector<4xi1>):
    "llvm.intr.masked.store"(%arg0, %arg1, %arg2) <{alignment = 4 : i32}> : (vector<4xi32>, !llvm.ptr, vector<4xi1>) -> ()
    "llvm.return"() : () -> ()
}

end

/-! ## Execution tests -/

section Tests

private def p : Pointer := ⟨⟨1⟩, 0⟩

/-- Block `1`: 8 bytes, `0x0000000200000001`, lanes `1` and `2`. -/
private def s0 : GlobalState :=
  ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 8 0x0000000200000001#64)]⟩⟩

private def mask (a b c d : BitVec 1) : ⟦Ty.vec 4 1⟧ :=
  #v[.value a, .value b, .value c, .value d]

private def nines : ⟦Ty.vec 4 32⟧ :=
  #v[.value 9, .value 9, .value 9, .value 9]

/-- The loaded vector, or `none` for UB. -/
private def loadOut (m : ⟦Ty.vec 4 1⟧) : Option ⟦Ty.vec 4 32⟧ :=
  match mload.eval 1 (mload.args (.value p) m nines) s0 with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard loadOut (mask 1 0 0 0) == some #v[.value 1, .value 9, .value 9, .value 9]
#guard loadOut (mask 1 1 0 0) == some #v[.value 1, .value 2, .value 9, .value 9]
-- the unset lanes past the block access nothing
#guard loadOut (mask 0 1 0 0) == some #v[.value 9, .value 2, .value 9, .value 9]
-- a set lane past the block: UB
#guard loadOut (mask 1 1 1 0) == none
-- a poison mask lane: UB
#guard loadOut #v[.value 1, .poison, .value 0, .value 0] == none

/-- Block `1`'s bytes after the store, or `none` for UB. -/
private def storeOut (m : ⟦Ty.vec 4 1⟧) : Option (BitVec 64) :=
  match mstore.eval 1 (mstore.args #v[.value 5, .value 6, .value 7, .value 8] (.value p) m) s0 with
  | .value (some _, s) => some (s.mem.readAt p 64)
  | _ => none

#guard storeOut (mask 0 1 0 0) == some 0x0000000600000001#64
#guard storeOut (mask 1 1 0 0) == some 0x0000000600000005#64
#guard storeOut (mask 0 0 0 0) == some 0x0000000200000001#64
#guard storeOut (mask 0 0 1 0) == none

end Tests

end MLIR.Tests.Syntax.Masked

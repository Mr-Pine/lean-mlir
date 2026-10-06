module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Global
public import SSA.Projects.RIR.Semantics.Operations.InboundsGep
meta import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR.Tests.Syntax.InboundsGep

@[expose] public section

private def flagOp (bits : Int) : MLIR.Op :=
  ⟨"llvm.getelementptr", [], [], [], .mk [.mk "noWrapFlags" (.int bits (.int 32))]⟩

#guard Translate.gepAllNoWrapFlags (flagOp 7)
#guard !Translate.gepAllNoWrapFlags (flagOp 1)
#guard !Translate.gepAllNoWrapFlags (flagOp 2)
#guard !Translate.gepAllNoWrapFlags (flagOp 3)
#guard !Translate.gepAllNoWrapFlags (flagOp 4)
#guard !Translate.gepAllNoWrapFlags (flagOp 6)
#guard !Translate.gepAllNoWrapFlags (flagOp 15)

-- Exact shape of the NAF/table indexing instructions in agave_avx2_double_base.mlir.
mlir_def tableIndex := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

mlir_def wideIndex := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i128):
    %0 = "llvm.getelementptr"(%arg0, %arg1) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i128) -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

private def state : GlobalState := (⟨default, default⟩ : GlobalState).alloca 32
private def ptr (offset : BitVec 64) : Pointer := ⟨⟨0⟩, offset⟩
private def result (f : Func) (args : Vals f.Γ.args) (s : GlobalState := state) :
    Option (PoisonOr Pointer) :=
  match f.eval 1 args s with
  | .value (some vs, _) =>
    match f.tRets, vs with
    | [.ptr], .cons v .nil => some v
    | _, _ => none
  | _ => none

#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 3)) == some (.value (ptr 24))
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 4)) == some (.value (ptr 32))
#guard result tableIndex (tableIndex.args (.value (ptr 32)) (.value 0)) == some (.value (ptr 32))
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 5)) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 32)) (.value 1)) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 33)) (.value 0)) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 8)) (.value (-1))) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value (2^61))) == some .poison
#guard result tableIndex (tableIndex.args (.value (ptr 0)) .poison) == some .poison
#guard result wideIndex (wideIndex.args (.value (ptr 0)) (.value (2^64))) == some .poison
-- Deliberate restricted-domain behavior: absent allocations are not silently treated as live.
#guard result tableIndex (tableIndex.args (.value (ptr 0)) (.value 0)) ⟨default, default⟩ == some .poison

-- The combined flags allow a negative *narrow* index multiplied by zero, but
-- wide negative truncation still violates nuw even if the final offset is zero.
#guard Operation.gepInboundsIndex 0 (.value (-1 : BitVec 32)) == .value 0
#guard Operation.gepInboundsIndex 0 (.value (-1 : BitVec 128)) == .poison

example (g : ByteGlobal) (id : BlockId) (m : MemoryState)
    (hlive : g.Present id m) (hsize : g.length < 2^63)
    (offsets : List Int)
    (hwithin : Operation.GepInboundsOffsets g.length 0 offsets) :
    Operation.gepInboundsLive m (.value (g.address id)) (offsets.map .value) =
      .value ((g.address id).add (BitVec.ofInt 64 offsets.sum)) := by
  apply Operation.gepInboundsLive_eq (ptr := g.address id)
    (block := ⟨g.length, g.bytes⟩) hlive hsize
  simpa [ByteGlobal.address] using hwithin

end
end LeanMLIR.RIR.Tests.Syntax.InboundsGep

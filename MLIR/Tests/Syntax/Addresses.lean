module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `ptrtoaddr` and `ptrtoint`: addresses of the state's unconstrained choice -/

namespace MLIR.Tests.Syntax.Addresses

@[expose] public section

/-- How far `q` is past `p`, as a vectorizer's alias check computes it. -/
mlir_def dist := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.ptrtoaddr"(%arg0) : (!llvm.ptr) -> i64
    %1 = "llvm.ptrtoaddr"(%arg1) : (!llvm.ptr) -> i64
    %2 = "llvm.sub"(%1, %0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%2) : (i64) -> ()
}

/-- An address's low 32 bits. -/
mlir_def low := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.ptrtoint"(%arg0) : (!llvm.ptr) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

end

/-! ## Execution tests -/

section Tests

/-- Block `k` at `k * 2^32 + 16`. -/
private instance spread : Unspecified :=
  ⟨fun k => BitVec.ofNat 64 (k.id * 2 ^ 32 + 16), fun _ _ _ => 0, fun _ _ _ => 0⟩

private def distOut (s : GlobalState) (p q : ⟦Ty.ptr⟧) : Option ⟦Ty.bv 64⟧ :=
  match dist.eval 1 (dist.args p q) s with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

-- in one block, the offsets' difference, whatever the addresses
#guard distOut ⟨⟨1⟩, ⟨∅⟩⟩ (.value ⟨⟨1⟩, 8⟩) (.value ⟨⟨1⟩, 40⟩) == some (.value 32)
#guard distOut ⟨⟨1⟩, @MemoryState.mk ∅ spread _⟩ (.value ⟨⟨1⟩, 8⟩) (.value ⟨⟨1⟩, 40⟩) ==
  some (.value 32)
-- across blocks, the choice's
#guard distOut ⟨⟨1⟩, @MemoryState.mk ∅ spread _⟩ (.value ⟨⟨1⟩, 0⟩) (.value ⟨⟨3⟩, 0⟩) ==
  some (.value 0x200000000)
#guard distOut ⟨⟨1⟩, ⟨∅⟩⟩ (.value .null) .poison == some .poison

#guard (match low.eval 1 (low.args (.value ⟨⟨5⟩, 4⟩)) ⟨⟨1⟩, @MemoryState.mk ∅ spread _⟩ with
  | .value (some (.cons v .nil), _) => v == .value 20
  | _ => false)

end Tests

/-! ## Steps -/

section Steps

-- `step_pure` reads the state's addresses
example (p : Pointer) (s : GlobalState) (hwf : s.WF) :
    dist.call (dist.args (.value p) (.value (p.add 8))) s = .value (.cons (.value 8) .nil, s) := by
  func_init
  block_init
  step_pure with a
  guard_hyp ha : a = S₀.mem.addr p.id + p.offset
  step_pure with b
  step_pure with d
  finish_block
  subst_vars
  have h : ∀ a o : BitVec 64, a + (o + 8#64) - (a + o) = 8#64 := by intro a o; bv_omega
  simp only [Pointer.add, h]
  rfl

end Steps

end MLIR.Tests.Syntax.Addresses

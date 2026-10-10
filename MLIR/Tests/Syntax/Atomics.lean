module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # Fences, atomic and volatile accesses: plain ones, as the model runs one thread -/

namespace MLIR.Tests.Syntax.Atomics

@[expose] public section

/-- zeroize's pattern: a volatile store, a compiler fence, then an atomic store and load. -/
mlir_def zeroize := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64):
    %0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    "llvm.store"(%0, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.fence"() <{ordering = 4 : i64}> : () -> ()
    "llvm.store"(%arg1, %arg0) <{alignment = 8 : i64, ordering = 2 : i64}> : (i64, !llvm.ptr) -> ()
    %1 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 7 : i64, syncscope = "singlethread"}> : (!llvm.ptr) -> i64
    %2 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    %3 = "llvm.add"(%1, %2) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%3) : (i64) -> ()
}

-- the fences translate to nothing
example : zeroize.entry.body.length = 6 := rfl

/-- A volatile store after the slot's lifetime: still UB. -/
mlir_def volatileAfterEnd := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %1 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%1) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%1) : (!llvm.ptr) -> ()
    "llvm.store"(%arg0, %1) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (i64) -> ()
}

end

/-! ## Execution tests -/

section Tests

private def p : Pointer := ⟨⟨1⟩, 0⟩

/-- `zeroize p x`'s result, or `none` for UB. -/
private def zeroizeOut (s : GlobalState) (x : BitVec 64) : Option ⟦Ty.bv 64⟧ :=
  match zeroize.eval 1 (zeroize.args (.value p) (.value x)) s with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard zeroizeOut ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 8 0)]⟩⟩ 21 == some (.value 42)
-- the volatile store's bounds are checked
#guard zeroizeOut ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 4 0)]⟩⟩ 21 == none

#guard (match volatileAfterEnd.eval 1 (volatileAfterEnd.args (.value 7)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some _, _) => false
  | _ => true)

end Tests

/-! ## Steps -/

section Steps

-- the accesses by `step_store`/`step_load`, as plain ones
example (q : Pointer) (x : BitVec 64) (s : GlobalState) (hwf : s.WF) (hq : Room s.mem q 64) :
    zeroize.call (zeroize.args (.value q) (.value x)) s =
      .value (.cons (.value (x + x)) .nil, { s with mem := (s.mem.storeAt q 0#64).storeAt q x }) := by
  func_init
  block_init
  step_pure
  step_store
  step_store
  step_load
  step_load
  step_pure
  finish_block
  rw [hS]

end Steps

end MLIR.Tests.Syntax.Atomics

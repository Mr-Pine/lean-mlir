module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # Unbound calls of library functions: their `LibFunc` meaning -/

namespace MLIR.Tests.Syntax.LibCalls

@[expose] public section

/-- `bcmp(a, b, n) == 0`, as Agave compares the recompressed `R`. -/
mlir_def same := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    %0 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %1 = "llvm.call"(%arg0, %arg1, %arg2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.nonnull, llvm.noundef}, {llvm.nonnull, llvm.noundef}, {}], callee = @bcmp, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> i32
    %2 = "llvm.icmp"(%1, %0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    "llvm.return"(%2) : (i1) -> ()
}

mlir_def order := {
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: i64):
    %0 = "llvm.call"(%arg0, %arg1, %arg2) <{callee = @memcmp, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> i32
    "llvm.return"(%0) : (i32) -> ()
}

/-- `sodium_memzero`'s FORTIFY call. -/
mlir_def wipe := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64, %arg2: i64):
    "llvm.call"(%arg0, %arg1, %arg2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.nonnull, llvm.noundef}, {llvm.noundef}, {llvm.noundef}], callee = @__explicit_bzero_chk, fastmathFlags = #llvm.fastmath<none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, i64, i64) -> ()
    "llvm.return"() : () -> ()
}

mlir_def fill := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i32, %arg2: i64):
    %0 = "llvm.call"(%arg0, %arg1, %arg2) <{callee = @memset_explicit, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, i32, i64) -> !llvm.ptr
    "llvm.call"(%arg0, %arg2) <{callee = @explicit_bzero, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, i64) -> ()
    "llvm.return"(%0) : (!llvm.ptr) -> ()
}

end

/-! ## Execution tests -/

section Tests

private def a : Pointer := ⟨⟨1⟩, 0⟩
private def b : Pointer := ⟨⟨2⟩, 0⟩

/-- `a` and `b`, 4 bytes each; `b`'s top byte undefined if `undef`. -/
private def s0 (x y : BitVec 32) (undef := false) : GlobalState :=
  ⟨⟨3⟩, ⟨Std.ExtHashMap.ofList [(⟨1⟩, .ofBytes 4 x),
    (⟨2⟩, if undef then ⟨4, y, 0x00FFFFFF, true, fun _ => none⟩ else .ofBytes 4 y)]⟩⟩

private def sameOut (s : GlobalState) (n : Nat) : Option ⟦Ty.bv 1⟧ :=
  match same.eval 1 (same.args (.value a) (.value b) (.value (BitVec.ofNat 64 n))) s with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard sameOut (s0 0x11223344 0x11223344) 4 == some (.value 1)
#guard sameOut (s0 0x11223344 0x99223344) 4 == some (.value 0)
-- the bytes compared only
#guard sameOut (s0 0x11223344 0x99223344) 3 == some (.value 1)
#guard sameOut (s0 0x11223344 0x11223344) 0 == some (.value 1)
-- out of bounds: UB; an undefined byte: poison
#guard sameOut (s0 0x11223344 0x11223344) 5 == none
#guard sameOut (s0 0x11223344 0x11223344 (undef := true)) 4 == some .poison
#guard sameOut (s0 0x11223344 0x11223344 (undef := true)) 3 == some (.value 1)

/-- `memcmp`'s sign: `-1`, `0` or `1`. -/
private def orderOut (x y : BitVec 32) : Option Int :=
  match order.eval 1 (order.args (.value a) (.value b) (.value 4)) (s0 x y) with
  | .value (some (.cons (.value r) .nil), _) => some (if r = 0 then 0 else if r.msb then -1 else 1)
  | _ => none

-- the lowest byte first, unsigned
#guard orderOut 0x11223344 0x11223344 == some 0
#guard orderOut 0x00000002 0xFF000001 == some 1
#guard orderOut 0xFF000001 0x00000002 == some (-1)
#guard orderOut 0x00000080 0x0000007F == some 1

/-- `a` after `wipe a n size`, or `none` for UB. -/
private def wipeOut (n size : BitVec 64) : Option (BitVec 32) :=
  match wipe.eval 1 (wipe.args (.value a) (.value n) (.value size)) (s0 0x11223344 0) with
  | .value (some _, s) => some (s.mem.readAt a 32)
  | _ => none

#guard wipeOut 2 (-1) == some 0x11220000
#guard wipeOut 2 4 == some 0x11220000
-- more than the object holds
#guard wipeOut 2 1 == none
#guard wipeOut 5 (-1) == none

#guard (match fill.eval 1 (fill.args (.value a) (.value 0x1AB) (.value 3)) (s0 0x11223344 0) with
  | .value (some (.cons p .nil), s) => p == .value a && s.mem.readAt a 32 == 0x11000000
  | _ => false)

end Tests

/-! ## Steps -/

section Steps

-- `step_call` with the library function's lemma
example (p q : Pointer) (s : GlobalState) (hwf : s.WF) (hp : Fits s.mem p 256)
    (hq : Fits s.mem q 256) (h : s.mem.readAt p 256 = s.mem.readAt q 256) :
    same.call (same.args (.value p) (.value q) (.value 32)) s = .value (.cons (.value 1) .nil, s) := by
  func_init
  block_init
  step_pure
  step_call using Operation.bcmp_eq with r
  step_pure [hr, Operation.bcmpResult_self]
  finish_block
  subst hS
  rfl

-- FORTIFY's check of an unknown object size passes
example (p : Pointer) (n : BitVec 64) (s : GlobalState) (hwf : s.WF)
    (hp : Room s.mem p (8 * n.toNat)) :
    wipe.call (wipe.args (.value p) (.value n) (.value (-1))) s =
      .value (.nil, { s with mem := s.mem.storeAt p (0 : BitVec (8 * n.toNat)) }) := by
  func_init
  block_init
  step_call using Operation.explicitBzeroChk_eq
  finish_block
  rw [hS]

end Steps

end MLIR.Tests.Syntax.LibCalls

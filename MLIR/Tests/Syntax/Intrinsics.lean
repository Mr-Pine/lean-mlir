module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # Comparison, min/max, byte swap and reduction intrinsics, vector casts and the empty `asm` -/

namespace MLIR.Tests.Syntax.Intrinsics

@[expose] public section

mlir_def cmps := {
  ^bb0(%arg0: i8, %arg1: i8):
    %0 = "llvm.intr.scmp"(%arg0, %arg1) : (i8, i8) -> i8
    %1 = "llvm.intr.ucmp"(%arg0, %arg1) : (i8, i8) -> i2
    "llvm.return"(%0, %1) : (i8, i2) -> ()
}

mlir_def cmpLanes := {
  ^bb0(%arg0: vector<2xi32>, %arg1: vector<2xi32>):
    %0 = "llvm.intr.scmp"(%arg0, %arg1) : (vector<2xi32>, vector<2xi32>) -> vector<2xi8>
    "llvm.return"(%0) : (vector<2xi8>) -> ()
}

mlir_def minMax := {
  ^bb0(%arg0: i32, %arg1: i32):
    %0 = "llvm.intr.umin"(%arg0, %arg1) : (i32, i32) -> i32
    %1 = "llvm.intr.umax"(%arg0, %arg1) : (i32, i32) -> i32
    %2 = "llvm.intr.smin"(%arg0, %arg1) : (i32, i32) -> i32
    %3 = "llvm.intr.smax"(%arg0, %arg1) : (i32, i32) -> i32
    "llvm.return"(%0, %1, %2, %3) : (i32, i32, i32, i32) -> ()
}

mlir_def swapLanes := {
  ^bb0(%arg0: vector<2xi32>):
    %0 = "llvm.intr.bswap"(%arg0) : (vector<2xi32>) -> vector<2xi32>
    "llvm.return"(%0) : (vector<2xi32>) -> ()
}

mlir_def andAll := {
  ^bb0(%arg0: vector<4xi8>):
    %0 = "llvm.intr.vector.reduce.and"(%arg0) : (vector<4xi8>) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

mlir_def casts := {
  ^bb0(%arg0: vector<2xi16>):
    %0 = "llvm.zext"(%arg0) : (vector<2xi16>) -> vector<2xi32>
    %1 = "llvm.sext"(%arg0) : (vector<2xi16>) -> vector<2xi32>
    %2 = "llvm.trunc"(%arg0) <{overflowFlags = 2 : i32}> : (vector<2xi16>) -> vector<2xi8>
    "llvm.return"(%0, %1, %2) : (vector<2xi32>, vector<2xi32>, vector<2xi8>) -> ()
}

/-- `asm("" : "+r"(x))`, a value barrier, as clang imports it. -/
mlir_def barrier := {
  ^bb0(%arg0: i8):
    %0 = "llvm.inline_asm"(%arg0) <{asm_dialect = 0 : i64, asm_string = "", constraints = "=r,0,~{dirflag},~{fpsr},~{flags}", tail_call_kind = #llvm.tailcallkind<tail>}> : (i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

example : barrier.entry.body = [.unop .copy (rir_dst% barrier.hty 0) (.arg 0 rfl)] := rfl

end

/-! ## Execution tests -/

section Tests

/-- `scmp` and `ucmp` of `x` and `y`. -/
private def cmpsOut (x y : ⟦Ty.bv 8⟧) : Option (⟦Ty.bv 8⟧ × ⟦Ty.bv 2⟧) :=
  match cmps.eval 1 (cmps.args x y) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons a (.cons b .nil)), _) => some (a, b)
  | _ => none

#guard cmpsOut (.value 1) (.value 2) == some (.value 0xFF, .value 3)
#guard cmpsOut (.value 2) (.value 2) == some (.value 0, .value 0)
-- `-1 < 1` signed, `0xFF > 1` unsigned
#guard cmpsOut (.value 0xFF) (.value 1) == some (.value 0xFF, .value 1)
#guard cmpsOut .poison (.value 1) == some (.poison, .poison)

#guard (match cmpLanes.eval 1
    (cmpLanes.args (Ty.wrap (t := .vec 2 32) #v[5, 7]) (Ty.wrap (t := .vec 2 32) #v[6, 7]))
    ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => v == Ty.wrap (t := .vec 2 8) #v[0xFF, 0]
  | _ => false)

/-- `umin`, `umax`, `smin`, `smax` of `x` and `y`. -/
private def minMaxOut (x y : BitVec 32) : Option (List ⟦Ty.bv 32⟧) :=
  match minMax.eval 1 (minMax.args (.value x) (.value y)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons a (.cons b (.cons c (.cons d .nil)))), _) => some [a, b, c, d]
  | _ => none

#guard minMaxOut 0xFFFFFFFF 1 == some [.value 1, .value 0xFFFFFFFF, .value 0xFFFFFFFF, .value 1]

#guard (match swapLanes.eval 1 (swapLanes.args (Ty.wrap (t := .vec 2 32) #v[0x11223344, 0xAABBCCDD]))
    ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => v == Ty.wrap (t := .vec 2 32) #v[0x44332211, 0xDDCCBBAA]
  | _ => false)

/-- `vector.reduce.and` of `v`. -/
private def andAllOut (v : ⟦Ty.vec 4 8⟧) : Option ⟦Ty.bv 8⟧ :=
  match andAll.eval 1 (andAll.args v) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons r .nil), _) => some r
  | _ => none

#guard andAllOut (Ty.wrap (t := .vec 4 8) #v[0xF3, 0x3F, 0xFF, 0x7B]) == some (.value 0x33)
#guard andAllOut #v[.value 0, .poison, .value 0, .value 0] == some .poison

-- lane-wise casts; `trunc nuw` of `0x100` is poison in its lane only
#guard (match casts.eval 1 (casts.args (Ty.wrap (t := .vec 2 16) #v[0x8001, 0x7F])) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons a (.cons b (.cons c .nil))), _) =>
    a == Ty.wrap (t := .vec 2 32) #v[0x8001, 0x7F] &&
      b == Ty.wrap (t := .vec 2 32) #v[0xFFFF8001, 0x7F] && c == #v[.poison, .value 0x7F]
  | _ => false)

-- the barrier returns its operand, poison included
#guard (match barrier.eval 1 (barrier.args (.value 0x5A)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => v == .value 0x5A
  | _ => false)
#guard (match barrier.eval 1 (barrier.args .poison) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => v == .poison
  | _ => false)

end Tests

/-! ## Steps -/

section Steps

-- each by `step_pure`
example (x y : BitVec 8) (s : GlobalState) (hwf : s.WF) :
    cmps.call (cmps.args (.value x) (.value y)) s =
      .value
        (.cons (.value (if x.slt y then -1 else if x = y then 0 else 1))
            (.cons (.value (if x.ult y then -1 else if x = y then 0 else 1)) .nil),
          s) := by
  func_init
  block_init
  step_pure with c
  step_pure with u
  finish_block
  subst_vars
  rfl

example (x : BitVec 8) (s : GlobalState) (hwf : s.WF) :
    barrier.call (barrier.args (.value x)) s = .value (.cons (.value x) .nil, s) := by
  func_init
  block_init
  step_pure
  finish_block
  subst_vars
  rfl

example (a b : BitVec 32) (s : GlobalState) (hwf : s.WF) :
    swapLanes.call (swapLanes.args (Ty.wrap (t := .vec 2 32) #v[a, b])) s =
      .value
        (.cons (Ty.wrap (t := .vec 2 32) #v[(Operation.bswap (.value a)).getValue,
          (Operation.bswap (.value b)).getValue]) .nil, s) := by
  func_init
  block_init
  step_pure with v
  finish_block
  subst_vars
  rfl

end Steps

end MLIR.Tests.Syntax.Intrinsics

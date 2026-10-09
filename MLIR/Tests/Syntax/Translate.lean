module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func
meta import MLIR.Syntax.Translate

/-! # `translate` against `mlir_def`, on `fd_f25519_is_zero`: eleven blocks and a `switch` -/

namespace MLIR.Tests.Syntax

@[expose] public section

mlir_def fd_f25519_is_zero :=
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.switch"(%4)[^bb9, ^bb1, ^bb5] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[0, 2251799813685229]> : vector<2xi64>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb1:  // pred: ^bb0
    %5 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %7 = "llvm.icmp"(%6, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%7)[^bb2, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %8 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %10 = "llvm.icmp"(%9, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%10)[^bb3, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb3:  // pred: ^bb2
    %11 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %12 = "llvm.load"(%11) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %13 = "llvm.icmp"(%12, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%13)[^bb4, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    %14 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %16 = "llvm.icmp"(%15, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%16, %1)[^bb10, ^bb9] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb5:  // pred: ^bb0
    %17 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %19 = "llvm.icmp"(%18, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%19)[^bb6, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb6:  // pred: ^bb5
    %20 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %22 = "llvm.icmp"(%21, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%22)[^bb7, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb7:  // pred: ^bb6
    %23 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %24 = "llvm.load"(%23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %25 = "llvm.icmp"(%24, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%25)[^bb8, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb8:  // pred: ^bb7
    %26 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %27 = "llvm.load"(%26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %28 = "llvm.icmp"(%27, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%28, %1)[^bb10, ^bb9] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb9:  // 9 preds: ^bb0, ^bb1, ^bb2, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
    "llvm.br"(%3)[^bb10] : (i32) -> ()
  ^bb10(%29: i32):  // 3 preds: ^bb4, ^bb8, ^bb9
    "llvm.return"(%29) : (i32) -> ()
}

/-- The same region, as an AST. -/
def fd_f25519_is_zero.region : MLIR.Region := mlir_region%
{
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %4 = "llvm.load"(%arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    "llvm.switch"(%4)[^bb9, ^bb1, ^bb5] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[0, 2251799813685229]> : vector<2xi64>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb1:  // pred: ^bb0
    %5 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %7 = "llvm.icmp"(%6, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%7)[^bb2, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:  // pred: ^bb1
    %8 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %9 = "llvm.load"(%8) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %10 = "llvm.icmp"(%9, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%10)[^bb3, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb3:  // pred: ^bb2
    %11 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %12 = "llvm.load"(%11) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %13 = "llvm.icmp"(%12, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%13)[^bb4, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb4:  // pred: ^bb3
    %14 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %15 = "llvm.load"(%14) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %16 = "llvm.icmp"(%15, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%16, %1)[^bb10, ^bb9] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb5:  // pred: ^bb0
    %17 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %19 = "llvm.icmp"(%18, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%19)[^bb6, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb6:  // pred: ^bb5
    %20 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %21 = "llvm.load"(%20) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %22 = "llvm.icmp"(%21, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%22)[^bb7, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb7:  // pred: ^bb6
    %23 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %24 = "llvm.load"(%23) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %25 = "llvm.icmp"(%24, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%25)[^bb8, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb8:  // pred: ^bb7
    %26 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %27 = "llvm.load"(%26) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %28 = "llvm.icmp"(%27, %0) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%28, %1)[^bb10, ^bb9] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
  ^bb9:  // 9 preds: ^bb0, ^bb1, ^bb2, ^bb3, ^bb4, ^bb5, ^bb6, ^bb7, ^bb8
    "llvm.br"(%3)[^bb10] : (i32) -> ()
  ^bb10(%29: i32):  // 3 preds: ^bb4, ^bb8, ^bb9
    "llvm.return"(%29) : (i32) -> ()
}

/-! The hand lift, for comparison. -/
namespace Hand

/-- `%arg0 = x`; the constants `%0 … %3`, the first limb `%4`; per checking block a limb pointer,
the limb and the comparison; `%29` the result, `^bb10`'s block argument. -/
abbrev fd_f25519_is_zero.Γ : Ctx :=
  ⟨30, [.ptr],
    [.bv 64, .bv 32, .bv 64, .bv 32, .bv 64,   -- %0 … %4
      .ptr, .bv 64, .bv 1,                     -- ^bb1: %5 … %7
      .ptr, .bv 64, .bv 1,                     -- ^bb2
      .ptr, .bv 64, .bv 1,                     -- ^bb3
      .ptr, .bv 64, .bv 1,                     -- ^bb4
      .ptr, .bv 64, .bv 1,                     -- ^bb5
      .ptr, .bv 64, .bv 1,                     -- ^bb6
      .ptr, .bv 64, .bv 1,                     -- ^bb7
      .ptr, .bv 64, .bv 1,                     -- ^bb8: %26 … %28
      .bv 32], rfl, 0, 0⟩                                 -- %29

/-- Only `^bb10` takes an argument, `%29`. -/
abbrev fd_f25519_is_zero.blockTys : Fin 11 → List Ty :=
  fun i => if i.val = 10 then [.bv 32] else []

/-- `^bb10`'s parameter is `%29`. -/
abbrev fd_f25519_is_zero.blockParams :
    (k : Fin 11) → Dsts fd_f25519_is_zero.Γ (fd_f25519_is_zero.blockTys k)
  | ⟨10, _⟩ => .cons ⟨29, rfl⟩ .nil
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ => .nil

namespace fd_f25519_is_zero

abbrev BB := BasicBlock fd_f25519_is_zero.Γ [.bv 32] fd_f25519_is_zero.blockTys

def bb0 : BB where
  body :=
    [ .const (2251799813685247 : BitVec 64) ⟨0, rfl⟩,
      .const (1 : BitVec 32) ⟨1, rfl⟩,
      .const (0 : BitVec 64) ⟨2, rfl⟩,
      .const (0 : BitVec 32) ⟨3, rfl⟩,
      .load ⟨4, rfl⟩ (.arg 0 rfl) ]
  -- limb 0 picks the chain: `0` for zero, `2^51 - 19` for `p`
  exit := .switch (.val 4 rfl) ⟨9, .nil⟩
    [(0#64, ⟨1, .nil⟩), (2251799813685229#64, ⟨5, .nil⟩)]

def bb1 : BB where
  body :=
    [ .unop (.gepConst 8) ⟨5, rfl⟩ (.arg 0 rfl),
      .load ⟨6, rfl⟩ (.val 5 rfl),
      .binop (.icmp .eq) ⟨7, rfl⟩ (.val 6 rfl) (.val 2 rfl) ]
  exit := .condBr (.val 7 rfl) ⟨2, .nil⟩ ⟨9, .nil⟩

def bb2 : BB where
  body :=
    [ .unop (.gepConst 16) ⟨8, rfl⟩ (.arg 0 rfl),
      .load ⟨9, rfl⟩ (.val 8 rfl),
      .binop (.icmp .eq) ⟨10, rfl⟩ (.val 9 rfl) (.val 2 rfl) ]
  exit := .condBr (.val 10 rfl) ⟨3, .nil⟩ ⟨9, .nil⟩

def bb3 : BB where
  body :=
    [ .unop (.gepConst 24) ⟨11, rfl⟩ (.arg 0 rfl),
      .load ⟨12, rfl⟩ (.val 11 rfl),
      .binop (.icmp .eq) ⟨13, rfl⟩ (.val 12 rfl) (.val 2 rfl) ]
  exit := .condBr (.val 13 rfl) ⟨4, .nil⟩ ⟨9, .nil⟩

def bb4 : BB where
  body :=
    [ .unop (.gepConst 32) ⟨14, rfl⟩ (.arg 0 rfl),
      .load ⟨15, rfl⟩ (.val 14 rfl),
      .binop (.icmp .eq) ⟨16, rfl⟩ (.val 15 rfl) (.val 2 rfl) ]
  -- all limbs zero: return `1`
  exit := .condBr (.val 16 rfl) ⟨10, .cons (.val 1 rfl) .nil⟩ ⟨9, .nil⟩

def bb5 : BB where
  body :=
    [ .unop (.gepConst 8) ⟨17, rfl⟩ (.arg 0 rfl),
      .load ⟨18, rfl⟩ (.val 17 rfl),
      .binop (.icmp .eq) ⟨19, rfl⟩ (.val 18 rfl) (.val 0 rfl) ]
  exit := .condBr (.val 19 rfl) ⟨6, .nil⟩ ⟨9, .nil⟩

def bb6 : BB where
  body :=
    [ .unop (.gepConst 16) ⟨20, rfl⟩ (.arg 0 rfl),
      .load ⟨21, rfl⟩ (.val 20 rfl),
      .binop (.icmp .eq) ⟨22, rfl⟩ (.val 21 rfl) (.val 0 rfl) ]
  exit := .condBr (.val 22 rfl) ⟨7, .nil⟩ ⟨9, .nil⟩

def bb7 : BB where
  body :=
    [ .unop (.gepConst 24) ⟨23, rfl⟩ (.arg 0 rfl),
      .load ⟨24, rfl⟩ (.val 23 rfl),
      .binop (.icmp .eq) ⟨25, rfl⟩ (.val 24 rfl) (.val 0 rfl) ]
  exit := .condBr (.val 25 rfl) ⟨8, .nil⟩ ⟨9, .nil⟩

def bb8 : BB where
  body :=
    [ .unop (.gepConst 32) ⟨26, rfl⟩ (.arg 0 rfl),
      .load ⟨27, rfl⟩ (.val 26 rfl),
      .binop (.icmp .eq) ⟨28, rfl⟩ (.val 27 rfl) (.val 0 rfl) ]
  -- the limbs of `p`: return `1`
  exit := .condBr (.val 28 rfl) ⟨10, .cons (.val 1 rfl) .nil⟩ ⟨9, .nil⟩

/-- Some limb did not match: return `0`. -/
def bb9 : BB where
  body := []
  exit := .br ⟨10, .cons (.val 3 rfl) .nil⟩

def bb10 : BB where
  body := []
  exit := .ret (.cons (.val 29 rfl) .nil)

end fd_f25519_is_zero

@[reducible] def fd_f25519_is_zero : Func where
  Γ := fd_f25519_is_zero.Γ
  tRets := [.bv 32]
  n := 11
  blockTys := fd_f25519_is_zero.blockTys
  blockParams := fd_f25519_is_zero.blockParams
  hhasBlock := by decide
  hentry := rfl
  blocks
    | ⟨0, _⟩ => fd_f25519_is_zero.bb0
    | ⟨1, _⟩ => fd_f25519_is_zero.bb1
    | ⟨2, _⟩ => fd_f25519_is_zero.bb2
    | ⟨3, _⟩ => fd_f25519_is_zero.bb3
    | ⟨4, _⟩ => fd_f25519_is_zero.bb4
    | ⟨5, _⟩ => fd_f25519_is_zero.bb5
    | ⟨6, _⟩ => fd_f25519_is_zero.bb6
    | ⟨7, _⟩ => fd_f25519_is_zero.bb7
    | ⟨8, _⟩ => fd_f25519_is_zero.bb8
    | ⟨9, _⟩ => fd_f25519_is_zero.bb9
    | ⟨10, _⟩ => fd_f25519_is_zero.bb10

/-- The argument: `%arg0 := x`. -/
def fd_f25519_is_zero.args (x : ⟦Ty.ptr⟧) : Vals fd_f25519_is_zero.Γ.args :=
  .cons x .nil

end Hand

-- `blockTys` is written differently; the context and the bodies are the same.
example : fd_f25519_is_zero.Γ = Hand.fd_f25519_is_zero.Γ := rfl
example : fd_f25519_is_zero.bb0.body = Hand.fd_f25519_is_zero.bb0.body := rfl
example : fd_f25519_is_zero.bb1.body = Hand.fd_f25519_is_zero.bb1.body := rfl
example : fd_f25519_is_zero.bb2.body = Hand.fd_f25519_is_zero.bb2.body := rfl
example : fd_f25519_is_zero.bb3.body = Hand.fd_f25519_is_zero.bb3.body := rfl
example : fd_f25519_is_zero.bb4.body = Hand.fd_f25519_is_zero.bb4.body := rfl
example : fd_f25519_is_zero.bb5.body = Hand.fd_f25519_is_zero.bb5.body := rfl
example : fd_f25519_is_zero.bb6.body = Hand.fd_f25519_is_zero.bb6.body := rfl
example : fd_f25519_is_zero.bb7.body = Hand.fd_f25519_is_zero.bb7.body := rfl
example : fd_f25519_is_zero.bb8.body = Hand.fd_f25519_is_zero.bb8.body := rfl
example : fd_f25519_is_zero.bb9.body = Hand.fd_f25519_is_zero.bb9.body := rfl
example : fd_f25519_is_zero.bb10.body = Hand.fd_f25519_is_zero.bb10.body := rfl

end

/-! ## Execution: the translated `Func`, `mlir_def`'s, and the hand lift's agree -/

section Tests

private def x : Pointer := ⟨⟨0⟩, 0⟩

/-- One 40-byte block holding `bytes`. -/
private def state (bytes : BitVec 320) : GlobalState :=
  ⟨⟨1⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, ⟨40, bytes⟩)]⟩⟩

/-- `f`'s result at a pointer to `bytes`, if `f` takes a pointer and returns an `i32`. -/
private def out (f : Func) (bytes : BitVec 320) (p : ⟦Ty.ptr⟧ := .value x) :
    Option (PoisonOr (BitVec 32)) :=
  if h : f.Γ.args = [.ptr] ∧ f.tRets = [.bv 32] then
    match f.eval 11 (h.1 ▸ .cons p .nil) (state bytes) with
    | .value (some vs, _) => match h.2 ▸ vs with | .cons v .nil => some v
    | _ => none
  else none

private def translated : Func :=
  match translate fd_f25519_is_zero.region with
  | .ok f => f
  | .error _ => fd_f25519_is_zero

#guard (translate fd_f25519_is_zero.region).toBool

private def inputs : List (BitVec 320 × PoisonOr (BitVec 32)) :=
  [ (0#320, .value 1#32),
    (0x0007ffffffffffff0007ffffffffffff0007ffffffffffff0007ffffffffffff0007ffffffffffed#320,
      .value 1#32),
    (1#320, .value 0#32),
    (0x0007fffffffffffe0007ffffffffffff0007ffffffffffff0007ffffffffffff0007ffffffffffed#320,
      .value 0#32),
    (0x0000000000000001000000000000000000000000000000000000000000000000000000000000000#320,
      .value 0#32) ]

#guard inputs.all fun (b, r) =>
  out translated b == some r && out fd_f25519_is_zero b == some r &&
    out (Hand.fd_f25519_is_zero) b == some r

-- A poison pointer is UB.
#guard (out translated 0#320 .poison).isNone && (out fd_f25519_is_zero 0#320 .poison).isNone

end Tests

/-! ## `translate`'s errors, and callees -/

#guard translate (mlir_region% {
  ^bb0(%arg0: i32, %arg1: i32):
    %0 = "llvm.udiv"(%arg0, %arg1) : (i32, i32) -> i32
    "llvm.return"(%0) : (i32) -> ()
}) matches .error "^bb0: %0 = \"llvm.udiv\"(%arg0, %arg1) : (i32, i32) -> i32: unsupported operation 'llvm.udiv'"

private def callsG : MLIR.Region := mlir_region% {
  ^bb0(%arg0: i64):
    %0 = "llvm.call"(%arg0) <{callee = @g}> : (i64) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

/-- `g x = x + 1`. -/
private def succ : Callee :=
  ⟨[.bv 64], [.bv 64], fun | .cons x .nil => pure (.cons (x >>= fun v => .value (v + 1)) .nil)⟩

#guard translate callsG matches .error "no callee bound for @g"
#guard (translate callsG (fun | "g" => some succ | _ => none)).toBool

#guard match translate callsG (fun | "g" => some succ | _ => none) with
  | .ok f =>
    if h : f.Γ.args = [.bv 64] ∧ f.tRets = [.bv 64] then
      match f.eval 1 (h.1 ▸ .cons (.value 41#64) .nil) ⟨default, default⟩ with
      | .value (some vs, _) => match h.2 ▸ vs with | .cons v .nil => v == .value 42#64
      | _ => false
    else false
  | .error _ => false

end MLIR.Tests.Syntax

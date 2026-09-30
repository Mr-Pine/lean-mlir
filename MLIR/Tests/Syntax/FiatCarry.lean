module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `mlir_def` on `fiat_25519_carry`: gep, loads, stores and overflow flags -/

namespace MLIR.Tests.Syntax

@[expose] public section

mlir_def fiat_25519_carry :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %3 = "llvm.load"(%arg1) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %4 = "llvm.lshr"(%3, %0) : (i64, i64) -> i64
    %5 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    %6 = "llvm.load"(%5) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %7 = "llvm.add"(%4, %6) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %8 = "llvm.lshr"(%7, %0) : (i64, i64) -> i64
    %9 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    %10 = "llvm.load"(%9) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %11 = "llvm.add"(%8, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %12 = "llvm.lshr"(%11, %0) : (i64, i64) -> i64
    %13 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    %14 = "llvm.load"(%13) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %15 = "llvm.add"(%12, %14) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %16 = "llvm.lshr"(%15, %0) : (i64, i64) -> i64
    %17 = "llvm.getelementptr"(%arg1) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    %18 = "llvm.load"(%17) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (!llvm.ptr) -> i64
    %19 = "llvm.add"(%16, %18) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %20 = "llvm.and"(%3, %1) : (i64, i64) -> i64
    %21 = "llvm.lshr"(%19, %0) : (i64, i64) -> i64
    %22 = "llvm.mul"(%21, %2) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %23 = "llvm.add"(%22, %20) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %24 = "llvm.lshr"(%23, %0) : (i64, i64) -> i64
    %25 = "llvm.and"(%7, %1) : (i64, i64) -> i64
    %26 = "llvm.add"(%24, %25) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %27 = "llvm.and"(%23, %1) : (i64, i64) -> i64
    %28 = "llvm.and"(%26, %1) : (i64, i64) -> i64
    %29 = "llvm.lshr"(%26, %0) : (i64, i64) -> i64
    %30 = "llvm.and"(%11, %1) : (i64, i64) -> i64
    %31 = "llvm.add"(%29, %30) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
    %32 = "llvm.and"(%15, %1) : (i64, i64) -> i64
    %33 = "llvm.and"(%19, %1) : (i64, i64) -> i64
    "llvm.store"(%27, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %34 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%28, %34) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %35 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 2>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%31, %35) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %36 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 3>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%32, %36) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    %37 = "llvm.getelementptr"(%arg0) <{elem_type = i64, inbounds, rawConstantIndices = array<i32: 4>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.store"(%33, %37) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag1]}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

/-! The hand lift, for comparison. -/
namespace Hand

/-- `%arg0 = out`, `%arg1 = x`. `%5, %9, %13, %17` and `%34 … %37` are limb pointers, everything
else is an `i64`. -/
abbrev fiat_25519_carry.Γ : Ctx :=
  ⟨[.ptr, .ptr],
    [.bv 64, .bv 64, .bv 64, .bv 64, .bv 64,   -- %0 … %4
      .ptr, .bv 64, .bv 64, .bv 64,            -- %5 … %8
      .ptr, .bv 64, .bv 64, .bv 64,            -- %9 … %12
      .ptr, .bv 64, .bv 64, .bv 64,            -- %13 … %16
      .ptr, .bv 64, .bv 64,                    -- %17 … %19
      .bv 64, .bv 64, .bv 64, .bv 64, .bv 64, .bv 64, .bv 64,   -- %20 … %26
      .bv 64, .bv 64, .bv 64, .bv 64, .bv 64, .bv 64, .bv 64,   -- %27 … %33
      .ptr, .ptr, .ptr, .ptr]⟩                 -- %34 … %37

abbrev fiat_25519_carry.blockTys : Fin 1 → List Ty := fun _ => []

abbrev fiat_25519_carry.blockParams : (k : Fin 1) → Dsts fiat_25519_carry.Γ (fiat_25519_carry.blockTys k) := fun _ => .nil

def fiat_25519_carry.entry : BasicBlock fiat_25519_carry.Γ [] fiat_25519_carry.blockTys where
  body :=
    [ .const (51 : BitVec 64) ⟨0, rfl⟩,
      .const (2251799813685247 : BitVec 64) ⟨1, rfl⟩,
      .const (19 : BitVec 64) ⟨2, rfl⟩,
      -- the carry chain through the five limbs
      .load ⟨3, rfl⟩ (.arg 1 rfl),
      .binop (.lshr false) ⟨4, rfl⟩ (.val 3 rfl) (.val 0 rfl),
      .unop (.gepConst 8) ⟨5, rfl⟩ (.arg 1 rfl),
      .load ⟨6, rfl⟩ (.val 5 rfl),
      .binop (.add {}) ⟨7, rfl⟩ (.val 4 rfl) (.val 6 rfl),
      .binop (.lshr false) ⟨8, rfl⟩ (.val 7 rfl) (.val 0 rfl),
      .unop (.gepConst 16) ⟨9, rfl⟩ (.arg 1 rfl),
      .load ⟨10, rfl⟩ (.val 9 rfl),
      .binop (.add {}) ⟨11, rfl⟩ (.val 8 rfl) (.val 10 rfl),
      .binop (.lshr false) ⟨12, rfl⟩ (.val 11 rfl) (.val 0 rfl),
      .unop (.gepConst 24) ⟨13, rfl⟩ (.arg 1 rfl),
      .load ⟨14, rfl⟩ (.val 13 rfl),
      .binop (.add {}) ⟨15, rfl⟩ (.val 12 rfl) (.val 14 rfl),
      .binop (.lshr false) ⟨16, rfl⟩ (.val 15 rfl) (.val 0 rfl),
      .unop (.gepConst 32) ⟨17, rfl⟩ (.arg 1 rfl),
      .load ⟨18, rfl⟩ (.val 17 rfl),
      .binop (.add {}) ⟨19, rfl⟩ (.val 16 rfl) (.val 18 rfl),
      -- the reduction: the top carry, times 19, back into limb 0, and one more carry
      .binop .and ⟨20, rfl⟩ (.val 3 rfl) (.val 1 rfl),
      .binop (.lshr false) ⟨21, rfl⟩ (.val 19 rfl) (.val 0 rfl),
      .binop (.mul { nsw := true, nuw := true }) ⟨22, rfl⟩ (.val 21 rfl) (.val 2 rfl),
      .binop (.add { nsw := true, nuw := true }) ⟨23, rfl⟩ (.val 22 rfl) (.val 20 rfl),
      .binop (.lshr false) ⟨24, rfl⟩ (.val 23 rfl) (.val 0 rfl),
      .binop .and ⟨25, rfl⟩ (.val 7 rfl) (.val 1 rfl),
      .binop (.add { nsw := true, nuw := true }) ⟨26, rfl⟩ (.val 24 rfl) (.val 25 rfl),
      .binop .and ⟨27, rfl⟩ (.val 23 rfl) (.val 1 rfl),
      .binop .and ⟨28, rfl⟩ (.val 26 rfl) (.val 1 rfl),
      .binop (.lshr false) ⟨29, rfl⟩ (.val 26 rfl) (.val 0 rfl),
      .binop .and ⟨30, rfl⟩ (.val 11 rfl) (.val 1 rfl),
      .binop (.add { nsw := true, nuw := true }) ⟨31, rfl⟩ (.val 29 rfl) (.val 30 rfl),
      .binop .and ⟨32, rfl⟩ (.val 15 rfl) (.val 1 rfl),
      .binop .and ⟨33, rfl⟩ (.val 19 rfl) (.val 1 rfl),
      -- the stores
      .store (.arg 0 rfl) (.val 27 rfl),
      .unop (.gepConst 8) ⟨34, rfl⟩ (.arg 0 rfl),
      .store (.val 34 rfl) (.val 28 rfl),
      .unop (.gepConst 16) ⟨35, rfl⟩ (.arg 0 rfl),
      .store (.val 35 rfl) (.val 31 rfl),
      .unop (.gepConst 24) ⟨36, rfl⟩ (.arg 0 rfl),
      .store (.val 36 rfl) (.val 32 rfl),
      .unop (.gepConst 32) ⟨37, rfl⟩ (.arg 0 rfl),
      .store (.val 37 rfl) (.val 33 rfl) ]
  -- llvm.return
  exit := .ret .nil

@[reducible] def fiat_25519_carry : Func where
  Γ := fiat_25519_carry.Γ
  tRets := []
  n := 1
  blockTys := fiat_25519_carry.blockTys
  blockParams := fiat_25519_carry.blockParams
  hhasBlock := by decide
  hentry := rfl
  blocks := fun _ => fiat_25519_carry.entry

/-- The arguments: `%arg0 := out`, `%arg1 := x`. -/
def fiat_25519_carry.args (out x : ⟦Ty.ptr⟧) : Vals fiat_25519_carry.Γ.args :=
  .cons out (.cons x .nil)

end Hand

example : fiat_25519_carry = Hand.fiat_25519_carry := rfl
example : fiat_25519_carry.args = Hand.fiat_25519_carry.args := rfl

/-- One carry pass over the 51-bit limbs, the top carry folded back into limb 0 times 19
(`2^255 ≡ 19 mod p`), then one more carry out of limb 0 and limb 1. -/
def fiat_25519_carry.spec (x : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 :=
  let mask := 2251799813685247#64  -- `2^51 - 1`
  let t1 := (x 0 >>> 51) + x 1
  let t2 := (t1 >>> 51) + x 2
  let t3 := (t2 >>> 51) + x 3
  let t4 := (t3 >>> 51) + x 4
  let u0 := (t4 >>> 51) * 19 + (x 0 &&& mask)
  let u1 := (u0 >>> 51) + (t1 &&& mask)
  fun
    | ⟨0, _⟩ => u0 &&& mask
    | ⟨1, _⟩ => u1 &&& mask
    | ⟨2, _⟩ => (u1 >>> 51) + (t2 &&& mask)
    | ⟨3, _⟩ => t3 &&& mask
    | ⟨4, _⟩ => t4 &&& mask

end

/-! ## Execution tests -/

section Tests

private def out : Pointer := ⟨⟨0⟩, 0⟩
private def x : Pointer := ⟨⟨1⟩, 0⟩

/-- Two 40-byte blocks: `out` zeroed, `x` holding `bytes`. -/
private def state (bytes : BitVec 320) : GlobalState :=
  ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, ⟨40, 0⟩), (⟨1⟩, ⟨40, bytes⟩)]⟩⟩

/-- Every limb `2^52 - 1`, so every limb carries. -/
private def xBytes : BitVec 320 :=
  0x000fffffffffffff000fffffffffffff000fffffffffffff000fffffffffffff000fffffffffffff#320

private def limbs (b : BitVec 320) : Fin 5 → BitVec 64 :=
  fun k => b.extractLsb' (64 * k.val) 64

/-- The output limbs, or `none` for UB / out of fuel. -/
private def outLimbs (o i : ⟦Ty.ptr⟧) : Option (Fin 5 → BitVec 64) :=
  match fiat_25519_carry.eval 1 (fiat_25519_carry.args o i) (state xBytes) with
  | .value (some .nil, s') => some (limbs (s'.mem.readAt out 320))
  | _ => none

#guard match outLimbs (.value out) (.value x) with
  | some r => (List.finRange 5).all fun k => r k == fiat_25519_carry.spec (limbs xBytes) k
  | none => false

-- A poison pointer is UB.
#guard (outLimbs .poison (.value x)).isNone

end Tests

end MLIR.Tests.Syntax

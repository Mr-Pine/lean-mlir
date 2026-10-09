module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `mlir_def` on the AVX-512 `fd_r43x6_repsqr_mul2`: a loop, calls and vector shuffles -/

namespace MLIR.Tests.Syntax.Avx512

@[expose] public section

/-- `<8 x i64>`. -/
abbrev V : Ty := .vec 8 64

/-- `fd_r43x6_sqr_fast`'s type. -/
abbrev SqrFast := Vals [V] → EffectM (Vals [V])

/-- `fd_r43x6_mul_fast`'s type. -/
abbrev MulFast := Vals [V, V] → EffectM (Vals [V])

/-- The `Func` returning `sqr x`. -/
@[reducible] def sqrFunc (sqr : SqrFast) : Func where
  Γ := ⟨1, [V], [V], rfl, 0, 0⟩
  tRets := [V]
  n := 1
  blockTys _ := []
  blockParams _ := .nil
  hhasBlock := by decide
  hentry := rfl
  blocks _ :=
    { body := [.call sqr (.cons (.arg 0 rfl) .nil) (.cons ⟨0, rfl⟩ .nil)]
      exit := .ret (.cons (.val 0 rfl) .nil) }

/-- The `Func` returning `mul x y`. -/
@[reducible] def mulFunc (mul : MulFast) : Func where
  Γ := ⟨1, [V, V], [V], rfl, 0, 0⟩
  tRets := [V]
  n := 1
  blockTys _ := []
  blockParams _ := .nil
  hhasBlock := by decide
  hentry := rfl
  blocks _ :=
    { body := [.call mul (.cons (.arg 0 rfl) (.cons (.arg 1 rfl) .nil)) (.cons ⟨0, rfl⟩ .nil)]
      exit := .ret (.cons (.val 0 rfl) .nil) }

mlir_def fd_r43x6_repsqr_mul2 (sqr : SqrFast) (mul : MulFast) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: vector<8xi64>, %arg2: vector<8xi64>, %arg3: !llvm.ptr, %arg4: vector<8xi64>, %arg5: vector<8xi64>, %arg6: i64):
    %0 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = dense<[19, 1, 1, 1, 1, 1, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 43, 40, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.poison"() : () -> vector<8xi64>
    %6 = "llvm.icmp"(%arg6, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%6, %arg4, %arg1, %arg1, %arg4, %arg6)[^bb2, ^bb1] <{operandSegmentSizes = array<i32: 1, 2, 3>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, i64) -> ()
  ^bb1(%7: vector<8xi64>, %8: vector<8xi64>, %9: i64):  // 2 preds: ^bb0, ^bb1
    %10 = "llvm.call"(%7) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %11 = "llvm.and"(%10, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "llvm.lshr"(%10, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %13 = "llvm.shufflevector"(%12, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %14 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%11, %1, %13) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %15 = "llvm.call"(%8) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_sqr_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>) -> vector<8xi64>
    %16 = "llvm.and"(%15, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %17 = "llvm.lshr"(%15, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %18 = "llvm.shufflevector"(%17, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %19 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%16, %1, %18) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %20 = "llvm.add"(%9, %0) <{overflowFlags = #llvm.overflow<nsw>}> : (i64, i64) -> i64
    %21 = "llvm.icmp"(%20, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%21, %19, %14, %14, %19, %20)[^bb2, ^bb1] <{loop_annotation = #loop_annotation, operandSegmentSizes = array<i32: 1, 2, 3>}> : (i1, vector<8xi64>, vector<8xi64>, vector<8xi64>, vector<8xi64>, i64) -> ()
  ^bb2(%22: vector<8xi64>, %23: vector<8xi64>):  // 2 preds: ^bb0, ^bb1
    %24 = "llvm.call"(%23, %arg2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %25 = "llvm.and"(%24, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %26 = "llvm.lshr"(%24, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %27 = "llvm.shufflevector"(%26, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %28 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%25, %1, %27) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %29 = "llvm.call"(%22, %arg5) <{CConv = #llvm.cconv<fastcc>, callee = @fd_r43x6_mul_fast, fastmathFlags = #llvm.fastmath<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %30 = "llvm.and"(%29, %3) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %31 = "llvm.lshr"(%29, %4) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %32 = "llvm.shufflevector"(%31, %5) <{mask = array<i32: 5, 0, 1, 2, 3, 4, 6, 7>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %33 = "x86vector.avx512.intr.vpmadd52l.uq.512"(%30, %1, %32) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%28, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.store"(%33, %arg3) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
  with @fd_r43x6_sqr_fast := sqrFunc sqr, @fd_r43x6_mul_fast := mulFunc mul

/-! The hand lift, for comparison. -/
namespace Hand

/-- `fd_r43x6_approx_carry_propagate`'s lane rotation (`Programs/Avx512/FoldUnsigned.lean`). -/
abbrev rot : Vector (Option (Fin (2 * 8))) 8 :=
  #v[some 5, some 0, some 1, some 2, some 3, some 4, some 6, some 7]

/-- `%arg0 = _za`, `%arg1 = xa`, `%arg2 = ya`, `%arg3 = _zb`, `%arg4 = xb`, `%arg5 = yb`, `%arg6 = n`;
`%7 %8 %9` the loop's `xa xb n`, `%22 %23` the exit's `xb xa`. -/
abbrev fd_r43x6_repsqr_mul2.Γ : Ctx :=
  ⟨34, [.ptr, V, V, .ptr, V, V, .bv 64],
    [.bv 64, V, .bv 64, V, V, V, .bv 1,                   -- %0 … %6
      V, V, .bv 64,                                        -- ^bb1: %7 … %9
      V, V, V, V, V, V, V, V, V, V, .bv 64, .bv 1,         -- %10 … %21
      V, V,                                                -- ^bb2: %22 %23
      V, V, V, V, V, V, V, V, V, V], rfl, 0, 0⟩                       -- %24 … %33

abbrev fd_r43x6_repsqr_mul2.blockTys : Fin 3 → List Ty
  | ⟨1, _⟩ => [V, V, .bv 64]
  | ⟨2, _⟩ => [V, V]
  | _ => []

abbrev fd_r43x6_repsqr_mul2.blockParams :
    (k : Fin 3) → Dsts fd_r43x6_repsqr_mul2.Γ (fd_r43x6_repsqr_mul2.blockTys k)
  | ⟨0, _⟩ => .nil
  | ⟨1, _⟩ => .cons ⟨7, rfl⟩ (.cons ⟨8, rfl⟩ (.cons ⟨9, rfl⟩ .nil))
  | ⟨2, _⟩ => .cons ⟨22, rfl⟩ (.cons ⟨23, rfl⟩ .nil)

namespace fd_r43x6_repsqr_mul2

abbrev BB := BasicBlock Γ [] blockTys

def bb0 : BB where
  body :=
    [ .const (-1 : BitVec 64) ⟨0, rfl⟩,
      .const (#v[19, 1, 1, 1, 1, 1, 0, 0] : Vector (BitVec 64) 8) ⟨1, rfl⟩,
      .const (0 : BitVec 64) ⟨2, rfl⟩,
      .const (#v[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207,
        1099511627775, 0, 0] : Vector (BitVec 64) 8) ⟨3, rfl⟩,
      .const (#v[43, 43, 43, 43, 43, 40, 0, 0] : Vector (BitVec 64) 8) ⟨4, rfl⟩,
      .poison ⟨5, rfl⟩,
      .binop (.icmp .eq) ⟨6, rfl⟩ (.arg 6 rfl) (.val 2 rfl) ]
  -- `n == 0`: straight to the multiplies
  exit := .condBr (.val 6 rfl) ⟨2, .cons (.arg 4 rfl) (.cons (.arg 1 rfl) .nil)⟩
    ⟨1, .cons (.arg 1 rfl) (.cons (.arg 4 rfl) (.cons (.arg 6 rfl) .nil))⟩

variable (sqr : SqrFast) (mul : MulFast)

/-- `FD_R43X6_SQR2_INL( xa, xa, xb, xb )`, then `n--`. -/
def bb1 : BB where
  body :=
    [ .call sqr (.cons (.val 7 rfl) .nil) (.cons ⟨10, rfl⟩ .nil),
      .binop (.vector .and) ⟨11, rfl⟩ (.val 10 rfl) (.val 3 rfl),
      .binop (.vector (.lshr false)) ⟨12, rfl⟩ (.val 10 rfl) (.val 4 rfl),
      .binop (.shufflevector rot) ⟨13, rfl⟩ (.val 12 rfl) (.val 5 rfl),
      .ternop .vpmadd52l ⟨14, rfl⟩ (.val 11 rfl) (.val 1 rfl) (.val 13 rfl),
      .call sqr (.cons (.val 8 rfl) .nil) (.cons ⟨15, rfl⟩ .nil),
      .binop (.vector .and) ⟨16, rfl⟩ (.val 15 rfl) (.val 3 rfl),
      .binop (.vector (.lshr false)) ⟨17, rfl⟩ (.val 15 rfl) (.val 4 rfl),
      .binop (.shufflevector rot) ⟨18, rfl⟩ (.val 17 rfl) (.val 5 rfl),
      .ternop .vpmadd52l ⟨19, rfl⟩ (.val 16 rfl) (.val 1 rfl) (.val 18 rfl),
      .binop (.add { nsw := true }) ⟨20, rfl⟩ (.val 9 rfl) (.val 0 rfl),
      .binop (.icmp .eq) ⟨21, rfl⟩ (.val 20 rfl) (.val 2 rfl) ]
  exit := .condBr (.val 21 rfl) ⟨2, .cons (.val 19 rfl) (.cons (.val 14 rfl) .nil)⟩
    ⟨1, .cons (.val 14 rfl) (.cons (.val 19 rfl) (.cons (.val 20 rfl) .nil))⟩

/-- `FD_R43X6_MUL2_INL( xa, xa, ya, xb, xb, yb )`, then `*_za = xa; *_zb = xb`. -/
def bb2 : BB where
  body :=
    [ .call mul (.cons (.val 23 rfl) (.cons (.arg 2 rfl) .nil)) (.cons ⟨24, rfl⟩ .nil),
      .binop (.vector .and) ⟨25, rfl⟩ (.val 24 rfl) (.val 3 rfl),
      .binop (.vector (.lshr false)) ⟨26, rfl⟩ (.val 24 rfl) (.val 4 rfl),
      .binop (.shufflevector rot) ⟨27, rfl⟩ (.val 26 rfl) (.val 5 rfl),
      .ternop .vpmadd52l ⟨28, rfl⟩ (.val 25 rfl) (.val 1 rfl) (.val 27 rfl),
      .call mul (.cons (.val 22 rfl) (.cons (.arg 5 rfl) .nil)) (.cons ⟨29, rfl⟩ .nil),
      .binop (.vector .and) ⟨30, rfl⟩ (.val 29 rfl) (.val 3 rfl),
      .binop (.vector (.lshr false)) ⟨31, rfl⟩ (.val 29 rfl) (.val 4 rfl),
      .binop (.shufflevector rot) ⟨32, rfl⟩ (.val 31 rfl) (.val 5 rfl),
      .ternop .vpmadd52l ⟨33, rfl⟩ (.val 30 rfl) (.val 1 rfl) (.val 32 rfl),
      .store (.arg 0 rfl) (.val 28 rfl),
      .store (.arg 3 rfl) (.val 33 rfl) ]
  exit := .ret .nil

end fd_r43x6_repsqr_mul2

open fd_r43x6_repsqr_mul2 in
/-- `fd_r43x6_repsqr_mul2`, calling `sqr` for `fd_r43x6_sqr_fast` and `mul` for
`fd_r43x6_mul_fast`. -/
@[reducible] def fd_r43x6_repsqr_mul2 (sqr : SqrFast) (mul : MulFast) : Func where
  Γ := fd_r43x6_repsqr_mul2.Γ
  tRets := []
  n := 3
  blockTys := fd_r43x6_repsqr_mul2.blockTys
  blockParams := fd_r43x6_repsqr_mul2.blockParams
  hhasBlock := by decide
  hentry := rfl
  blocks
    | ⟨0, _⟩ => bb0
    | ⟨1, _⟩ => bb1 sqr
    | ⟨2, _⟩ => bb2 mul

/-- The arguments: `_za xa ya _zb xb yb n`. -/
def fd_r43x6_repsqr_mul2.args (za : ⟦Ty.ptr⟧) (xa ya : ⟦V⟧) (zb : ⟦Ty.ptr⟧) (xb yb : ⟦V⟧)
    (n : ⟦Ty.bv 64⟧) : Vals fd_r43x6_repsqr_mul2.Γ.args :=
  .cons za (.cons xa (.cons ya (.cons zb (.cons xb (.cons yb (.cons n .nil))))))

end Hand

example (sqr : SqrFast) (mul : MulFast) :
    fd_r43x6_repsqr_mul2 sqr mul = Hand.fd_r43x6_repsqr_mul2 (sqrFunc sqr).call (mulFunc mul).call :=
  rfl
example : fd_r43x6_repsqr_mul2.args = Hand.fd_r43x6_repsqr_mul2.args := rfl

end

/-! ## Execution tests -/

section Tests

private def p : Nat := 2 ^ 255 - 19

/-- The field element of r43x6 lanes `0 … 5`, mod `p`. -/
private def value (v : Vector (BitVec 64) 8) : Nat :=
  (List.range 6).foldl (fun acc i => acc + v[i]!.toNat * 2 ^ (43 * i)) 0 % p

/-- `N` as unreduced r43x6 lanes: 43-bit limbs, then one unit of each limb pushed down a lane,
and lane 5 unmasked, so the fold after the callee has carries everywhere. -/
private def unreduced (N : Nat) : Vector (BitVec 64) 8 :=
  let l := (List.range 6).map fun i => if i < 5 then N / 2 ^ (43 * i) % 2 ^ 43 else N / 2 ^ 215
  let l := (List.range 6).map fun i =>
    l[i]! + (if i < 5 ∧ l[i + 1]! > 0 then 2 ^ 43 else 0) - (if 0 < i ∧ l[i]! > 0 then 1 else 0)
  Vector.ofFn fun i => if i.val < 6 then BitVec.ofNat 64 l[i.val]! else 0

private def lanesOf (x : ⟦V⟧) : Vector (BitVec 64) 8 := x.map (·.toOption.getD 0)

/-- Reference callees: the product mod `p`, plus `2^9 p`, unreduced: lanes stay below `2^51`. -/
private def sqrRef : SqrFast
  | .cons x .nil => pure (.cons ((unreduced (value (lanesOf x) ^ 2 % p + 2 ^ 9 * p)).map .value) .nil)
private def mulRef : MulFast
  | .cons x (.cons y .nil) =>
    pure (.cons ((unreduced (value (lanesOf x) * value (lanesOf y) % p + 2 ^ 9 * p)).map .value) .nil)

private def za : Pointer := ⟨⟨0⟩, 0⟩
private def zb : Pointer := ⟨⟨1⟩, 0⟩

/-- Two zeroed 64-byte blocks. -/
private def state : GlobalState :=
  ⟨⟨2⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, ⟨64, 0⟩), (⟨1⟩, ⟨64, 0⟩)]⟩⟩

private def lanes8 (x : Nat) : ⟦V⟧ := (unreduced x).map .value

/-- `*_za ≡ xa^(2^n) ya` and `*_zb ≡ xb^(2^n) yb` mod `p`. -/
private def check (xa ya xb yb n : Nat) : Bool :=
  match (fd_r43x6_repsqr_mul2 sqrRef mulRef).eval (n + 3)
      (fd_r43x6_repsqr_mul2.args (.value za) (lanes8 xa) (lanes8 ya) (.value zb) (lanes8 xb)
        (lanes8 yb) (.value (BitVec.ofNat 64 n))) state with
  | .value (some .nil, s') =>
    let ra := s'.mem.readAt za 512
    let rb := s'.mem.readAt zb 512
    let rl (r : BitVec 512) : Vector (BitVec 64) 8 := Vector.ofFn fun i => r.extractLsb' (i.val * 64) 64
    value (rl ra) == xa ^ (2 ^ n) * ya % p && value (rl rb) == xb ^ (2 ^ n) * yb % p
  | _ => false

-- `n = 0` skips the loop; `n = 1, 3` run it
#guard check 3 5 7 11 0
#guard check 3 5 7 11 1
#guard check (2 ^ 250 + 12345) (2 ^ 200 + 1) (p - 1) (p - 2) 3

end Tests

end MLIR.Tests.Syntax.Avx512

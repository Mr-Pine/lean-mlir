module

public import MLIR.Syntax.Elab
public import MLIR.Run.BasicBlock
public import MLIR.Run.Memory
public import MLIR.Run.Vector
public import MLIR.Run.Tactic
meta import MLIR.Semantics.Func

/-! # `mlir_def` on the AVX-512 `fd_f25519_sub`: the hand lift, its tests and its proof -/

namespace MLIR.Tests.Syntax.Avx512

@[expose] public section

mlir_def fd_f25519_sub :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = dense<[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631, 1099510579199, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %1 = "llvm.mlir.constant"() <{value = dense<[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207, 1099511627775, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %2 = "llvm.mlir.constant"() <{value = dense<[43, 43, 43, 43, 43, 40, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %3 = "llvm.mlir.constant"() <{value = dense<[5, 0, 1, 2, 3, 4, 8, 8]> : vector<8xi64>}> : () -> vector<8xi64>
    %4 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi64>}> : () -> vector<8xi64>
    %5 = "llvm.mlir.constant"() <{value = dense<18> : vector<8xi64>}> : () -> vector<8xi64>
    %6 = "llvm.mlir.constant"() <{value = dense<[-1, 0, 0, 0, 0, 0, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %7 = "llvm.mlir.constant"() <{value = dense<[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0]> : vector<8xi64>}> : () -> vector<8xi64>
    %8 = "llvm.load"(%arg1) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %9 = "llvm.load"(%arg2) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (!llvm.ptr) -> vector<8xi64>
    %10 = "llvm.sub"(%8, %9) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %11 = "llvm.add"(%10, %0) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %12 = "llvm.and"(%11, %1) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %13 = "llvm.ashr"(%11, %2) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %14 = "x86vector.avx512.intr.vpermi2var.q.512"(%13, %3, %4) : (vector<8xi64>, vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %15 = "llvm.mul"(%14, %5) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %16 = "llvm.and"(%15, %6) : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %17 = "llvm.add"(%14, %7) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %18 = "llvm.add"(%17, %12) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    %19 = "llvm.add"(%18, %16) <{overflowFlags = #llvm.overflow<none>}> : (vector<8xi64>, vector<8xi64>) -> vector<8xi64>
    "llvm.store"(%19, %arg0) <{alignment = 64 : i64, ordering = 0 : i64, tbaa = [#tbaa_tag]}> : (vector<8xi64>, !llvm.ptr) -> ()
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}

/-! The hand lift, for comparison. -/
namespace Hand

/-- `%arg0 = r`, `%arg1 = a`, `%arg2 = b`; `%0 … %19` all `<8 x i64>`. -/
abbrev fd_f25519_sub.Γ : Ctx :=
  ⟨20, [.ptr, .ptr, .ptr],
    [.vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64,
      .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64,
      .vec 8 64, .vec 8 64, .vec 8 64, .vec 8 64], rfl, 0, 0⟩

/-- The lanes of an `<8 x i64>`. -/
abbrev V8 := Vector (BitVec 64) 8

abbrev fd_f25519_sub.blockTys : Fin 1 → List Ty := fun _ => []

abbrev fd_f25519_sub.blockParams : (k : Fin 1) → Dsts fd_f25519_sub.Γ (fd_f25519_sub.blockTys k) :=
  fun _ => .nil

def fd_f25519_sub.entry : BasicBlock fd_f25519_sub.Γ [.ptr] fd_f25519_sub.blockTys where
  body :=
    [ .const (#v[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631,
        1099510579199, 0, 0] : V8) ⟨0, rfl⟩,
      .const (#v[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207,
        1099511627775, 0, 0] : V8) ⟨1, rfl⟩,
      .const (#v[43, 43, 43, 43, 43, 40, 0, 0] : V8) ⟨2, rfl⟩,
      .const (#v[5, 0, 1, 2, 3, 4, 8, 8] : V8) ⟨3, rfl⟩,
      .const (.replicate 8 0 : V8) ⟨4, rfl⟩,
      .const (.replicate 8 18 : V8) ⟨5, rfl⟩,
      .const (#v[-1, 0, 0, 0, 0, 0, 0, 0] : V8) ⟨6, rfl⟩,
      .const (#v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0] : V8) ⟨7, rfl⟩,
      .load ⟨8, rfl⟩ (.arg 1 rfl),
      .load ⟨9, rfl⟩ (.arg 2 rfl),
      .binop (.vector (.sub {})) ⟨10, rfl⟩ (.val 8 rfl) (.val 9 rfl),
      .binop (.vector (.add {})) ⟨11, rfl⟩ (.val 10 rfl) (.val 0 rfl),
      .binop (.vector .and) ⟨12, rfl⟩ (.val 11 rfl) (.val 1 rfl),
      .binop (.vector (.ashr false)) ⟨13, rfl⟩ (.val 11 rfl) (.val 2 rfl),
      .ternop .vpermi2var ⟨14, rfl⟩ (.val 13 rfl) (.val 3 rfl) (.val 4 rfl),
      .binop (.vector (.mul {})) ⟨15, rfl⟩ (.val 14 rfl) (.val 5 rfl),
      .binop (.vector .and) ⟨16, rfl⟩ (.val 15 rfl) (.val 6 rfl),
      .binop (.vector (.add {})) ⟨17, rfl⟩ (.val 14 rfl) (.val 7 rfl),
      .binop (.vector (.add {})) ⟨18, rfl⟩ (.val 17 rfl) (.val 12 rfl),
      .binop (.vector (.add {})) ⟨19, rfl⟩ (.val 18 rfl) (.val 16 rfl),
      .store (.arg 0 rfl) (.val 19 rfl) ]
  exit := .ret (.cons (.arg 0 rfl) .nil)

@[reducible] def fd_f25519_sub : Func where
  Γ := fd_f25519_sub.Γ
  tRets := [.ptr]
  n := 1
  blockTys := fd_f25519_sub.blockTys
  blockParams := fd_f25519_sub.blockParams
  hhasBlock := by decide
  hentry := rfl
  blocks := fun _ => fd_f25519_sub.entry

/-- The arguments: `%arg0 := r`, `%arg1 := a`, `%arg2 := b`. -/
def fd_f25519_sub.args (r a b : ⟦Ty.ptr⟧) : Vals fd_f25519_sub.Γ.args :=
  .cons r (.cons a (.cons b .nil))

end Hand

example : fd_f25519_sub = Hand.fd_f25519_sub := rfl
example : fd_f25519_sub.args = Hand.fd_f25519_sub.args := rfl

open Hand (V8)

/-- The lanes of `x`, lane 0 lowest. -/
def lanes (x : BitVec 512) : V8 :=
  Vector.ofFn fun i => x.extractLsb' (i.val * 64) 64

/-- `fd_r43x6_fold_signed(fd_r43x6_sub_fast(a, b))`, as compiled: `a - b + (p - _b)`, then the
shift-and-add `fd_r43x6_approx_carry_propagate`, then `+ _b`. -/
def fd_f25519_sub.spec (a b : V8) : V8 :=
  -- `p - _b`, the masks `_m43`/`_m40`, the shifts, and the bias `_b`
  let pb : V8 := #v[8795933638637, 8796091973631, 8796091973631, 8796091973631, 8796091973631,
    1099510579199, 0, 0]
  let m : V8 := #v[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207,
    1099511627775, 0, 0]
  let sh : V8 := #v[43, 43, 43, 43, 43, 40, 0, 0]
  let _b : V8 := #v[159383552, 1048576, 1048576, 1048576, 1048576, 1048576, 0, 0]
  let _x := Vector.zipWith (· + ·) (Vector.zipWith (· - ·) a b) pb
  let _xl := Vector.zipWith (· &&& ·) _x m
  let _xh := Vector.zipWith (fun x s => x.sshiftRight s.toNat) _x sh
  let _c : V8 := #v[_xh[5], _xh[0], _xh[1], _xh[2], _xh[3], _xh[4], 0, 0]
  let _d : V8 := #v[18 * _c[0], 0, 0, 0, 0, 0, 0, 0]
  Vector.zipWith (· + ·) (Vector.zipWith (· + ·) (Vector.zipWith (· + ·) _c _b) _xl) _d

end

/-! ## Execution tests -/

section Tests

private def r : Pointer := ⟨⟨0⟩, 0⟩
private def a : Pointer := ⟨⟨1⟩, 0⟩
private def b : Pointer := ⟨⟨2⟩, 0⟩

/-- Pack eight 64-bit lanes, lane 0 lowest. -/
private def pack (l : List Nat) : BitVec 512 :=
  l.foldr (fun x acc => acc <<< 64 ||| BitVec.ofNat 512 x) 0

/-- The field element of r43x6 lanes: `Σ lane_i * 2^(43 i)` over lanes `0 … 5`, mod `p`. -/
private def value (x : BitVec 512) : Nat :=
  (List.range 6).foldl (fun acc i => acc + (x.extractLsb' (64 * i) 64).toNat * 2 ^ (43 * i)) 0 %
    (2 ^ 255 - 19)

/-- Three 64-byte blocks: `r` zeroed, `a` and `b` holding `ab` and `bb`. -/
private def state (ab bb : BitVec 512) : GlobalState :=
  ⟨⟨3⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, .ofBytes 64 0), (⟨1⟩, .ofBytes 64 ab), (⟨2⟩, .ofBytes 64 bb)]⟩⟩

/-- `r` is returned and holds `a - b` mod `p`, with lanes 6 and 7 zero. -/
private def check (ab bb : BitVec 512) : Bool :=
  match fd_f25519_sub.eval 1 (fd_f25519_sub.args (.value r) (.value a) (.value b)) (state ab bb) with
  | .value (some (.cons ret .nil), s') =>
    let out := s'.mem.readAt r 512
    ret == .value r && out.extractLsb' 384 128 == 0 &&
      value out == (value ab + (2 ^ 255 - 19) - value bb) % (2 ^ 255 - 19)
  | _ => false

-- small limbs, `a > b` and `a < b`
#guard check (pack [7, 6, 5, 4, 3, 2]) (pack [1, 2, 3, 4, 5, 6])
#guard check (pack [1, 0, 0, 0, 0, 0]) (pack [2, 0, 0, 0, 0, 0])

-- full 43-bit limbs (40 bits on top) on both sides
#guard check (pack [2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 40 - 1])
  (pack [2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 40 - 1])
#guard check (pack [0, 0, 0, 0, 0, 0])
  (pack [2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 43 - 1, 2 ^ 40 - 1])

-- `r` holds `spec a b`
#guard match fd_f25519_sub.eval 1
    (fd_f25519_sub.args (.value r) (.value a) (.value b)) (state (pack [7, 6, 5]) (pack [9])) with
  | .value (some _, s') =>
    s'.mem.readAt r 512 == BitVec.packLanes (fd_f25519_sub.spec (lanes (pack [7, 6, 5])) (lanes (pack [9])))
  | _ => false

-- a poison pointer is UB
#guard match fd_f25519_sub.eval 1 (fd_f25519_sub.args (.value r) .poison (.value b))
    (state 0 0) with
  | .value _ => false
  | _ => true

end Tests

/-! ## Specification -/

section Spec

/-- `sub` stores `spec a b` at `r` and returns `r`. `r` may alias `a` or `b`. -/
public theorem fd_f25519_sub.call_eq (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : Fits s.mem r 512) (ha : Fits s.mem a 512) (hb : Fits s.mem b 512) :
    fd_f25519_sub.call (fd_f25519_sub.args (.value r) (.value a) (.value b)) s =
      .value (.cons (.value r) .nil,
        { s with
          mem := s.mem.storeAt r
            (BitVec.packLanes (fd_f25519_sub.spec (lanes (s.mem.readAt a 512))
              (lanes (s.mem.readAt b 512)))) }) := by
  func_init
  block_init
  step_pure with p
  step_pure with reduced_mask
  step_pure with shift_amounts
  step_pure with rotl_idxs
  step_pure with zero
  step_pure with eightteen
  step_pure with first_elem_mask
  step_pure with bv
  step_load with x
  step_load with y
  step_pure opaque
  step_pure opaque with sub_fast
  -- fold_signed
  step_pure opaque named transparent
  step_pure opaque [hshift_amounts] named transparent
  step_pure [hrotl_idxs, hzero, expandOfFn, Ty.wrap_vec] named transparent
  step_pure opaque [heightteen] with multiplied
  step_pure opaque [hfirst_elem_mask, hmultiplied, expandOfFn, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.and_zero] named
  step_pure
  step_pure
  step_pure
  step_store
  finish_block
  rw [hS]
  subst_vars
  congr 1; congr 1; congr 1; congr 1; congr 1
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|_|_|_|_|i := i
  all_goals try simp [spec, lanes, Ty.extractVecElem_eq]
  all_goals try omega
  -- lane 0: `(c * 18) &&& -1 = 18 * c`
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
    BitVec.mul_comm]

end Spec

end MLIR.Tests.Syntax.Avx512

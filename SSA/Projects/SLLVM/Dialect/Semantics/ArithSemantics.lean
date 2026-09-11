/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanMLIR.Dialects.LLVM.Semantics
import SSA.Projects.SLLVM.Dialect.Semantics.EffectM
import SSA.Projects.SLLVM.Tactic.SimpSet

/-- `x.canBe y` returns true when `x` can be refined into a bitvector value `y`.
That is, when `x` is poison or `x` is equal to `value y`. -/
@[simp_sllvm]
def LLVM.IntW.canBe (x : LLVM.IntW w) (y : BitVec w) : Bool :=
  x = .poison ∨ x = .value y

namespace LeanMLIR.SLLVM

/-- An LLVM pointer, or `poison` -/
def Ptr : Type := PoisonOr Pointer

/-- The block `llvm.mlir.zero` points at. Reserved: it is the one id no
`alloca` may hand out and no global may be loaded at, so that a null pointer
aliases nothing. `alloca` takes `AllocState.nextFreeBlock` and never rewinds,
so a state whose counter starts above `0` -- which every loaded module's does,
`GlobalState.withGlobal` allocating the same way -- never names it. The model
does not *enforce* the reservation: `ptricmp` compares pointers, so a spec
whose region null-checks a live pointer carries `id ≠ nullBlock` itself. -/
def nullBlock : BlockId := ⟨0⟩

/-- The null pointer, `llvm.mlir.zero` at `!llvm.ptr`. Not poison: C code
returns it as a sentinel and branches on it, so it is a definite value -- one
that is never live, by `nullBlock`'s reservation. -/
def Ptr.null : SLLVM.Ptr := .value ⟨nullBlock, 0#64⟩

/-- `llvm.icmp eq`/`ne` at `!llvm.ptr` (`eq` selects which): the null check a
caller does on a failure sentinel. Poison in either operand is poison out;
two pointers are equal exactly when block and offset are. LLVM's provenance
rules make this weaker in general -- comparing pointers into distinct objects
is unspecified -- but every use here compares against `null`. -/
@[simp_sllvm]
def ptricmp (eq : Bool) (x y : SLLVM.Ptr) : LLVM.IntW 1 :=
  match x, y with
  | .value a, .value b => .value (if (a == b) == eq then 1#1 else 0#1)
  | _, _ => .poison

@[simp_sllvm]
theorem ptricmp_value (eq : Bool) (a b : Pointer) :
    ptricmp eq (.value a) (.value b) = .value (if (a == b) == eq then 1#1 else 0#1) := rfl

/-- Not a `simp` lemma: specs state the sentinel as `Ptr.null`, and rewriting
it away would leave both spellings in play. `ptricmp`'s reduction wants it, so
it is named. -/
theorem null_eq_value : Ptr.null = .value ⟨nullBlock, 0#64⟩ := rfl

/-- `llvm.select` at `!llvm.ptr`: `LLVM.select`'s rule at pointer type. A
poison condition is poison out; otherwise the chosen operand, poison or not,
passes through unchanged. -/
@[simp_sllvm]
def ptrselect (c : LLVM.IntW 1) (x y : SLLVM.Ptr) : SLLVM.Ptr :=
  match c with
  | .value b => if b = 1#1 then x else y
  | .poison => .poison

@[simp_sllvm]
theorem ptrselect_value (b : BitVec 1) (x y : SLLVM.Ptr) :
    ptrselect (.value b) x y = if b = 1#1 then x else y := rfl

/-! ### funnel shift -/

/-- `llvm.intr.fshl` on bare bitvectors: concatenate `a` (high) with `b` (low),
shift the `2w`-bit result left by `n mod w`, keep the high `w` bits.

`n` is taken modulo `w`, which is what LLVM specifies for `fshl` -- unlike
`shl`, an over-long shift amount is defined rather than poison. -/
def fshlBV {w : Nat} (a b : BitVec w) (n : BitVec w) : BitVec w :=
  ((a ++ b) <<< (n.toNat % w)).extractLsb' w w

/-- `llvm.intr.fshl`, poison-propagating: poison in any operand is poison out.
-/
@[simp_sllvm]
def fshl {w : Nat} (a b n : LLVM.IntW w) : LLVM.IntW w :=
  match a, b, n with
  | .value a, .value b, .value n => .value (fshlBV a b n)
  | _, _, _ => .poison

@[simp_sllvm]
theorem fshl_value {w : Nat} (a b n : BitVec w) :
    fshl (.value a) (.value b) (.value n) = .value (fshlBV a b n) := rfl

/-- `llvm.intr.fshr` on bare bitvectors: the low `w` bits of `a ++ b` shifted
right by `n mod w`. -/
def fshrBV {w : Nat} (a b : BitVec w) (n : BitVec w) : BitVec w :=
  ((a ++ b) >>> (n.toNat % w)).extractLsb' 0 w

/-- `llvm.intr.fshr`, poison-propagating. -/
@[simp_sllvm]
def fshr {w : Nat} (a b n : LLVM.IntW w) : LLVM.IntW w :=
  match a, b, n with
  | .value a, .value b, .value n => .value (fshrBV a b n)
  | _, _, _ => .poison

@[simp_sllvm]
theorem fshr_value {w : Nat} (a b n : BitVec w) :
    fshr (.value a) (.value b) (.value n) = .value (fshrBV a b n) := rfl

/-- Byte-reverse a `w`-bit value: byte `i` of the result is byte `k-1-i` of the
input, where `k = w / 8`. A `w` that is not a multiple of 8 keeps only the whole
bytes, which no producer emits and LLVM does not define either. -/
def bswapBV {w : Nat} (x : BitVec w) : BitVec w :=
  (List.range (w / 8)).foldl
    (fun acc i => acc ||| (((x >>> (8 * i)) &&& 0xFF#w) <<< (w - 8 - 8 * i))) 0#w

/-- `llvm.intr.bswap`, poison-propagating. -/
@[simp_sllvm]
def bswap {w : Nat} (x : LLVM.IntW w) : LLVM.IntW w :=
  match x with
  | .value x => .value (bswapBV x)
  | .poison => .poison

@[simp_sllvm]
theorem bswap_value {w : Nat} (x : BitVec w) : bswap (.value x) = .value (bswapBV x) := rfl

/-! ### min / max -/

/-- `llvm.intr.smin`, poison-propagating. No flags: the minimum of two values
is always one of them, so it cannot overflow. -/
@[simp_sllvm]
def smin {w : Nat} (a b : LLVM.IntW w) : LLVM.IntW w :=
  match a, b with
  | .value a, .value b => .value (if a.slt b then a else b)
  | _, _ => .poison

@[simp_sllvm]
theorem smin_value {w : Nat} (a b : BitVec w) :
    smin (.value a) (.value b) = .value (if a.slt b then a else b) := rfl

/-! ### div / rem -/

@[simp_sllvm]
def udiv (x y : LLVM.IntW w) (flag : LLVM.ExactFlag) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    pure <| LLVM.udiv x y flag

@[simp_sllvm]
def sdiv (x y : LLVM.IntW w) (flag : LLVM.ExactFlag) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    pure <| LLVM.sdiv x y flag

@[simp_sllvm]
def urem (x y : LLVM.IntW w) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    pure <| LLVM.urem x y

@[simp_sllvm]
def srem (x y : LLVM.IntW w) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    pure <| LLVM.srem x y

/-! ### aggregates in registers -/

/-- `llvm.insertvalue` on the flat model of aggregate registers: replace the
`fieldW` bits of `agg` at bit offset `offBits` by `v`.

Poison: a poison field poisons the whole result, and so does a poison
aggregate -- except when the field covers every bit of the aggregate, which is
what `undef` followed by one `insertvalue` produces, and where LLVM's answer is
just the field. LLVM tracks poison per field and `IntW` only per bitvector, so
outside that case the model is deliberately the conservative one. -/
def insertvalue {aggW fieldW : Nat} (offBits : Nat)
    (agg : LLVM.IntW aggW) (v : LLVM.IntW fieldW) : LLVM.IntW aggW := do
  let v ← v
  if offBits = 0 ∧ fieldW = aggW then
    return v.setWidth aggW
  let agg ← agg
  let mask : BitVec aggW := (BitVec.allOnes fieldW).setWidth aggW <<< offBits
  return (agg &&& ~~~mask) ||| (v.setWidth aggW <<< offBits)

/-! ### pointer arithmetic -/

def ptradd (p : SLLVM.Ptr) (x : LLVM.IntW 64) : SLLVM.Ptr := do
  let p ← p
  let x ← x
  return { p with offset := p.offset + x}

/-- `getelementptr` with one leading dynamic index and constant trailing
indices: `ptradd` by `strideBytes * i + offsetBytes`, where the stride is the
element type's size and the offset accumulates the constant struct-field and
array indices. `inbounds` is not modelled, so an out-of-bounds gep that LLVM
makes poison stays a plain pointer here -- more defined than LLVM. -/
def gep (p : SLLVM.Ptr) (strideBytes offsetBytes : Nat) (i : LLVM.IntW 64) : SLLVM.Ptr :=
  ptradd p (LLVM.add (LLVM.mul i (LLVM.const? 64 strideBytes)) (LLVM.const? 64 offsetBytes))

/-!
**SIMPLIFICATION**
We deliberately don't support int-to-ptr nor ptr-to-int casts
-/

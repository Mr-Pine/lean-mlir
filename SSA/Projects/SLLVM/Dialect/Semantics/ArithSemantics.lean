/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanMLIR.Dialects.LLVM.Semantics
public import SSA.Projects.SLLVM.Dialect.Semantics.EffectM
public import SSA.Projects.SLLVM.Tactic.SimpSet

@[expose] public section

/-- `x.canBe y` returns true when `x` can be refined into a bitvector value `y`.
That is, when `x` is poison or `x` is equal to `value y`. -/
@[simp_sllvm]
def LLVM.IntW.canBe (x : LLVM.IntW w) (y : BitVec w) : Bool :=
  x = .poison ∨ x = .value y

namespace LeanMLIR.SLLVM

/-- An LLVM pointer, or `poison` -/
@[implicit_reducible]
def Ptr : Type :=
  PoisonOr Pointer

/-- The block `llvm.mlir.zero` points at. Reserved: it is the one id no
`alloca` may hand out and no global may be loaded at, so that a null pointer
aliases nothing. `alloca` takes `AllocState.nextFreeBlock` and never rewinds,
so a state whose counter starts above `0` -- which every loaded module's does,
`GlobalState.withGlobal` allocating the same way -- never names it. The model
does not *enforce* the reservation: `ptricmp` compares pointers, so a spec
whose region null-checks a live pointer carries `id ≠ nullBlock` itself. -/
def nullBlock : BlockId :=
  ⟨0⟩

/-- The null pointer, `llvm.mlir.zero` at `!llvm.ptr`. Not poison: C code
returns it as a sentinel and branches on it, so it is a definite value -- one
that is never live, by `nullBlock`'s reservation. -/
def Ptr.null : SLLVM.Ptr :=
  .value ⟨nullBlock, 0#64⟩

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
    ptricmp eq (.value a) (.value b) = .value (if (a == b) == eq then 1#1 else 0#1) :=
  rfl

/-- Not a `simp` lemma: specs state the sentinel as `Ptr.null`, and rewriting
it away would leave both spellings in play. `ptricmp`'s reduction wants it, so
it is named. -/
theorem null_eq_value : Ptr.null = .value ⟨nullBlock, 0#64⟩ :=
  rfl

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
    ptrselect (.value b) x y = if b = 1#1 then x else y :=
  rfl

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
    fshl (.value a) (.value b) (.value n) = .value (fshlBV a b n) :=
  rfl

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
    fshr (.value a) (.value b) (.value n) = .value (fshrBV a b n) :=
  rfl

/-- Vector funnel shifts apply the scalar operation independently to each lane.
A poison operand poisons only its corresponding result lane. -/
@[simp_sllvm]
def vfshl {l w : Nat} (a b n : Vector (LLVM.IntW w) l) : Vector (LLVM.IntW w) l :=
  Vector.ofFn fun i => fshl a[i] b[i] n[i]

@[simp_sllvm]
def vfshr {l w : Nat} (a b n : Vector (LLVM.IntW w) l) : Vector (LLVM.IntW w) l :=
  Vector.ofFn fun i => fshr a[i] b[i] n[i]

@[simp]
theorem vfshl_getElem {l w : Nat} (a b n : Vector (LLVM.IntW w) l) (i : Fin l) :
    (vfshl a b n)[i] = fshl a[i] b[i] n[i] := by simp [vfshl]

@[simp]
theorem vfshr_getElem {l w : Nat} (a b n : Vector (LLVM.IntW w) l) (i : Fin l) :
    (vfshr a b n)[i] = fshr a[i] b[i] n[i] := by simp [vfshr]

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
theorem bswap_value {w : Nat} (x : BitVec w) : bswap (.value x) = .value (bswapBV x) :=
  rfl

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
    smin (.value a) (.value b) = .value (if a.slt b then a else b) :=
  rfl

/-- Unsigned minimum and maximum propagate poison from either operand. -/
@[simp_sllvm]
def umin {w : Nat} (a b : LLVM.IntW w) : LLVM.IntW w :=
  match a, b with
  | .value a, .value b => .value (if a.ult b then a else b)
  | _, _ => .poison

@[simp_sllvm]
def umax {w : Nat} (a b : LLVM.IntW w) : LLVM.IntW w :=
  match a, b with
  | .value a, .value b => .value (if a.ult b then b else a)
  | _, _ => .poison

/-- Vector min/max apply unsigned comparison independently to each lane. -/
def vumin {l w : Nat} (a b : Vector (LLVM.IntW w) l) : Vector (LLVM.IntW w) l :=
  Vector.ofFn fun i => umin a[i.val] b[i.val]

def vumax {l w : Nat} (a b : Vector (LLVM.IntW w) l) : Vector (LLVM.IntW w) l :=
  Vector.ofFn fun i => umax a[i.val] b[i.val]

/-- Vector freeze follows the existing scalar `LLVM.freeze` convention:
a defined lane is unchanged, and a poison lane becomes the fixed value zero.
This is a deterministic choice allowed by LLVM freeze, not an enumeration
of every choice in LLVM's nondeterministic semantics. Separate uses of the
result observe the same chosen value. -/
def vfreeze {l w : Nat} (a : Vector (LLVM.IntW w) l) : Vector (LLVM.IntW w) l :=
  a.map LLVM.freeze

@[simp_sllvm]
theorem vfreeze_lane {l w : Nat} (a : Vector (LLVM.IntW w) l) (i : Fin l) :
    (vfreeze a)[i.val] = LLVM.freeze a[i.val] := by
  simp only [vfreeze, Vector.getElem_map]

@[simp_sllvm]
theorem vfreeze_defined {l w : Nat} (a : Vector (BitVec w) l) :
    vfreeze (a.map PoisonOr.value) = a.map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [vfreeze, Vector.getElem_map, LLVM.freeze]

/-- A scalar condition selects the same arm for every vector lane. Poison in
the unselected arm is ignored; a poison condition poisons every result lane. -/
def vselectScalar {l w : Nat} (c : LLVM.IntW 1) (a b : Vector (LLVM.IntW w) l) :
    Vector (LLVM.IntW w) l := Vector.ofFn fun i => LLVM.select c a[i] b[i]

@[simp_sllvm]
theorem vselectScalar_lane {l w : Nat} (c : LLVM.IntW 1)
    (a b : Vector (LLVM.IntW w) l) (i : Fin l) :
    (vselectScalar c a b)[i.val] = LLVM.select c a[i.val] b[i.val] := by
  simp [vselectScalar]

/-- Integer vector casts apply the scalar operation, including all flags,
independently to each lane. -/
def vzext {l w : Nat} (w' : Nat) (a : Vector (LLVM.IntW w) l)
    (flag : LLVM.NonNegFlag := {}) : Vector (LLVM.IntW w') l :=
  a.map (fun x => LLVM.zext w' x flag)

def vsext {l w : Nat} (w' : Nat) (a : Vector (LLVM.IntW w) l) :
    Vector (LLVM.IntW w') l := a.map (LLVM.sext w')

def vtrunc {l w : Nat} (w' : Nat) (a : Vector (LLVM.IntW w) l)
    (flags : LLVM.NoWrapFlags := {}) : Vector (LLVM.IntW w') l :=
  a.map (fun x => LLVM.trunc w' x flags)

@[simp_sllvm]
theorem vzext_lane {l w : Nat} (w' : Nat) (a : Vector (LLVM.IntW w) l)
    (flag : LLVM.NonNegFlag) (i : Fin l) :
    (vzext w' a flag)[i.val] = LLVM.zext w' a[i.val] flag := by
  simp only [vzext, Vector.getElem_map]

@[simp_sllvm]
theorem vsext_lane {l w : Nat} (w' : Nat) (a : Vector (LLVM.IntW w) l) (i : Fin l) :
    (vsext w' a)[i.val] = LLVM.sext w' a[i.val] := by
  simp only [vsext, Vector.getElem_map]

@[simp_sllvm]
theorem vtrunc_lane {l w : Nat} (w' : Nat) (a : Vector (LLVM.IntW w) l)
    (flags : LLVM.NoWrapFlags) (i : Fin l) :
    (vtrunc w' a flags)[i.val] = LLVM.trunc w' a[i.val] flags := by
  simp only [vtrunc, Vector.getElem_map]

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
def insertvalue {aggW fieldW : Nat} (offBits : Nat) (agg : LLVM.IntW aggW) (v : LLVM.IntW fieldW) :
    LLVM.IntW aggW := do
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
  return { p with offset := p.offset + x }

/-- `getelementptr` with one leading dynamic index and constant trailing
indices: `ptradd` by `strideBytes * i + offsetBytes`, where the stride is the
element type's size and the offset accumulates the constant struct-field and
array indices. `inbounds` is not modelled, so an out-of-bounds gep that LLVM
makes poison stays a plain pointer here -- more defined than LLVM. -/
def gep (p : SLLVM.Ptr) (strideBytes offsetBytes : Nat) (i : LLVM.IntW 64) : SLLVM.Ptr :=
  ptradd p (LLVM.add (LLVM.mul i (LLVM.const? 64 strideBytes)) (LLVM.const? 64 offsetBytes))

/-- `getelementptr` with constant indices only: `ptradd` by `offsetBytes`. -/
def gepConst (p : SLLVM.Ptr) (offsetBytes : Nat) : SLLVM.Ptr :=
  ptradd p (LLVM.const? 64 offsetBytes)

/-- `getelementptr` with two dynamic indices: the first steps over whole
`elem_type`s and the constants after it walk to an array, which the second
indexes. That is exactly a `gep` into the array's address, so it is defined as
one -- lemmas about `gep` apply to each stage. -/
def gep2 (p : SLLVM.Ptr) (stride₀ offset₀ stride₁ offset₁ : Nat) (i j : LLVM.IntW 64) : SLLVM.Ptr :=
  gep (gep p stride₀ offset₀ i) stride₁ offset₁ j

/-!
**SIMPLIFICATION**
We deliberately don't support int-to-ptr nor ptr-to-int casts
-/

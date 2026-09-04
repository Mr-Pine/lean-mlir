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

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import Mathlib.Tactic.IntervalCases

/-!
# Shared lane semantics for the `fd_r43x6` denotation proofs

The `Avx512/Denote/` theorems all derive, instruction by instruction, the lane
expression a lifted `fd_r43x6` program computes. This file holds what those
derivations share:

* the `vpmadd52l`/`vpmadd52h` lane functions `mulLo52`/`mulHi52`, in terms of
  which every derived lane expression is stated;
* `toBitVecValue`/`hvecOfBv`, the bridges from ℕ-vectors to dialect values;
* the per-opcode tactics `denote_dense`, `denote_shuffle`, `denote_vecbin` and
  `denote_vpmadd52`, which reduce one `denote_step_all` hypothesis to the
  explicit vector it denotes.

The tactics work lanewise on 8-lane `vector<8xi64>` values; they are used on
goals of the shape `v<i> = <explicit vector>` produced by `denote_step_all`
(see `MLIR/DenoteStep.lean`).
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

def toBitVecValue (w: Nat) {n: Nat} (v: Vector Nat n): Vector (PoisonOr (BitVec w)) n :=
  v.map (fun i => PoisonOr.value <| BitVec.ofNat w i)

def hvecOfBv (w : Nat) {n : Nat} (v : Vector Nat n) : HVector TyDenote.toType [SLLVM.Ty.arith (.vector n (.bitvec (.concrete w)))] :=
  [toBitVecValue w v]ₕ

/-- Low 52 bits of the 104-bit product of the low 52 bits of `a` and `b` --
the `vpmadd52l` lane, with a zero addend. -/
def mulLo52 (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((a.toNat % 2 ^ 52) * (b.toNat % 2 ^ 52) % 2 ^ 52)

/-- Bits 103:52 of that product -- the `vpmadd52h` lane, with a zero addend. -/
def mulHi52 (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((a.toNat % 2 ^ 52) * (b.toNat % 2 ^ 52) / 2 ^ 52)

/-- `x &&& -1 = x`. The all-ones mask lanes normalise to the 64-bit all-ones
*literal*, which `simp` no longer recognises as `BitVec.allOnes`, so the
standard `BitVec.and_allOnes` never fires on its own. -/
theorem and_allOnes_64 (v : BitVec 64) : v &&& 18446744073709551615#64 = v := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes]

/-- `denote_dense hv` proves a goal `v = toBitVecValue w #v[…]`, given the
`denote_step_all` hypothesis `hv : v = (… .constDense …).denoteOp1 V` for a
`llvm.mlir.constant dense<[…]>` instruction.

The two sides are built differently — `LLVM.Ty.dense` uses `Vector.ofFn` and
`BitVec.ofInt`, `toBitVecValue` uses `Vector.map` and `BitVec.ofNat` — so they
are not definitionally equal and have to be compared lanewise. The right-hand
side may be a local `let` (e.g. `x0Shifts`); `+zetaDelta` unfolds it. -/
macro "denote_dense " h:term : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp +zetaDelta only [HVector.head, toBitVecValue, LLVM.Ty.dense]
             ext i hi
             simp only [Vector.getElem_ofFn, Vector.getElem_map]
             interval_cases i <;> rfl))

/-- `denote_shuffle hv` proves a goal `v = #v[…].map PoisonOr.value` given the
`denote_step_all` hypothesis for an `llvm.shufflevector` instruction.

`LLVM.Ty.shufflevector` builds the result with `Vector.ofFn` over a per-lane
`if`-chain on the mask, so the two sides are compared lanewise. `hi` comes out
as `i < mask.length`; `simp at hi` turns that into `i < 8` so `interval_cases`
can split. Each lane then reduces the mask `if`s and looks the operand up in
the valuation (`singleton`/`ofPair` unfold to `.cons`, so `cons_last` and
friends fire). -/
macro "denote_shuffle " h:term : tactic =>
  `(tactic| (simp [$h:term, Expr.denoteOp1, Expr.denoteOp, Expr.denoteOpPure]
             simp_peephole
             simp +zetaDelta only [HVector.head, LLVM.Ty.shufflevector]
             ext i hi
             simp only [Vector.getElem_ofFn]
             simp at hi
             interval_cases i
             all_goals simp +zetaDelta [Ctxt.Valuation.singleton, Ctxt.Valuation.ofPair,
               Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
               LLVM.Ty.poison, add_assoc]
             -- `wwl_slide` operands built with `Vector.replicate`/`append`
             -- index by computation rather than by a `simp` lemma.
             all_goals try rfl))

/-- `denote_vecbin hv` proves a goal `v = #v[…].map PoisonOr.value` given the
`denote_step_all` hypothesis for a vector `llvm.shl`, `llvm.and`, `llvm.add`
or `llvm.mul`.

The op denotes as `Vector.ofFn fun i => binaryDenote .shl a[i] b[i]`, so the
sides are compared lanewise. Each lane unfolds through `LLVM.shl` to `shl?`,
whose `if op2 ≥ w` guard discharges because the shift amounts here are small.

Note `apply Vector.ext` rather than `ext`: the equation's type is
`⟦SLLVMTy.arith …⟧`, which `ext` will not match syntactically, but `apply`
unifies with `Vector.ext` up to defeq. -/
macro "denote_vecbin " h:term : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta
               [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, LLVM.and, LLVM.and?,
                LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?, toBitVecValue, and_allOnes_64,
                LLVM.Ty.poison, add_assoc]
             all_goals try rfl))

/-- `denote_vpmadd52 hv` proves a goal `v = #v[…].map PoisonOr.value` for an
AVX-512 IFMA `vpmadd52l`/`vpmadd52h` instruction, lanewise as `denote_vecbin`.
An operand may be a block argument, so the valuation constructors are in the
simp set. -/
macro "denote_vpmadd52 " h:term : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta
               [LLVM.Ty.vpmadd52, LLVM.Ty.vpmadd52Lane, toBitVecValue,
                Ctxt.Valuation.singleton, Ctxt.Valuation.ofPair,
                Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
                mulLo52, mulHi52, Nat.mul_mod, Nat.mod_mod_of_dvd]))

end Firedancer.Avx512

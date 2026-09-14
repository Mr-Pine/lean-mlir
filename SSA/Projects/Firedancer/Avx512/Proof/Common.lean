/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Avx512.Spec.Common
import Mathlib.Tactic.IntervalCases

/-!
# Shared lane semantics for the `fd_r43x6` proofs

The `Avx512/Proof/` theorems derive, instruction by instruction, what a lifted
`fd_r43x6` program computes — directly at the ℕ level: every intermediate is
stated as `BitVec.ofNat 64` of an expression over the limb functions `pl`/`ph`
of `Spec/Common.lean`, so the derivation ends at the specified limbs rather
than at a `BitVec` lane expression needing a separate transfer.

This file holds what those derivations share:

* `toBitVecValue`/`hvecOfBv`, the bridges from ℕ-vectors to dialect values;
* `phRaw`, the `vpmadd52h` lane before its `2^9` prescaling, and the shift
  lemmas that fuse `BitVec.ofNat` through `<<<`;
* the per-opcode tactics `denote_dense`, `denote_shuffle`, `denote_vecbin`
  and `denote_vpmadd52`, which reduce one `denote_step_all` hypothesis to the
  explicit vector it denotes.

## The `with` clause

Reading a `vpmadd52` lane at the ℕ level needs to know that its operands are
already reduced mod `2^52`, and reading a shuffle needs the contract's zero
lanes. Those facts are hypotheses of the theorem being proved and differ per
program, so the tactics take them as a trailing `with` list of simp lemmas.
Each `Proof/fd_r43x6_*.lean` wraps them in a file-local macro that supplies
its own bound set once (escaping macro hygiene with `Lean.mkIdent`), rather
than repeating it at every instruction.

The tactics work lanewise on 8-lane `vector<8xi64>` values; they are used on
goals of the shape `v<i> = <explicit vector>` produced by `denote_step_all`
(see `MLIR/DenoteStep.lean`).
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The type every `fd_r43x6` value has: `vector<8xi64>`. Spelled here once --
`argTys` arguments and `Cfg` contexts both need it written out. -/
abbrev V8 : SLLVM.Ty := SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))

def toBitVecValue (w: Nat) {n: Nat} (v: Vector Nat n): Vector (PoisonOr (BitVec w)) n :=
  v.map (fun i => PoisonOr.value <| BitVec.ofNat w i)

def hvecOfBv (w : Nat) {n : Nat} (v : Vector Nat n) : HVector TyDenote.toType [SLLVM.Ty.arith (.vector n (.bitvec (.concrete w)))] :=
  [toBitVecValue w v]ₕ

/-- The `vpmadd52h` lane before its `2^9` prescaling: `ph a b = phRaw a b * 2^9`.
The instruction produces bits 103:52 of the product; the source shifts that
left by 9 to line it up with the next limb, and `ph` folds the two together. -/
def phRaw (a b : ℕ) : ℕ := a * b / 2^52

theorem phRaw_shl9 (a b : ℕ) : phRaw a b * 2^9 = ph a b := rfl

/-- `2^52 ∣ 2^64`, in the literal form `simp`'s `Nat.reducePow` leaves behind:
the `vpmadd52` lane truncates its operands mod `2^52` inside a mod `2^64`
value, and `Nat.mod_mod_of_dvd` collapses the two. -/
theorem dvd52_64 : (4503599627370496 : ℕ) ∣ 18446744073709551616 := ⟨4096, by norm_num⟩

/-! Shifts by the ℕ amounts that occur. `simp` has already turned the `BitVec`
shift amount into its `toNat` by the time these fire, and the right-hand sides
are in the multiplied-out form the lane expressions use. -/

theorem ofNat_shl1' (a : ℕ) :
    (BitVec.ofNat 64 a) <<< (1 : ℕ) = BitVec.ofNat 64 (2 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]

theorem ofNat_shl9' (a : ℕ) :
    (BitVec.ofNat 64 a) <<< (9 : ℕ) = BitVec.ofNat 64 (a * 512) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem ofNat_shl7' (a : ℕ) :
    (BitVec.ofNat 64 a) <<< (7 : ℕ) = BitVec.ofNat 64 (a * 128) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

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
             simp_denote_only
             simp +zetaDelta only [HVector.head, toBitVecValue, LLVM.Ty.dense]
             ext i hi
             simp only [Vector.getElem_ofFn, Vector.getElem_map]
             interval_cases i <;> rfl))

/-- `denote_shuffle hv with h…` proves a goal `v = toBitVecValue 64 #v[…]`
given the `denote_step_all` hypothesis for an `llvm.shufflevector`.

`LLVM.Ty.shufflevector` builds the result with `Vector.ofFn` over a per-lane
`if`-chain on the mask, so the two sides are compared lanewise. `hi` comes out
as `i < mask.length`; `simp at hi` turns that into `i < 8` so `interval_cases`
can split. Each lane then reduces the mask `if`s and looks the operand up in
the valuation (`singleton`/`ofPair` unfold to `.cons`, so `cons_last` and
friends fire).

This is where the contract's zero lanes are consumed: passing `x[7] = 0` in
the `with` list rewrites that lane to `0` as it is read out of the valuation,
so the products it would feed are never formed. -/
macro "denote_shuffle " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp [$h:term, Expr.denoteOp1, Expr.denoteOp, Expr.denoteOpPure]
             simp_denote_only
             simp +zetaDelta only [HVector.head, LLVM.Ty.shufflevector]
             ext i hi
             simp only [Vector.getElem_ofFn]
             simp at hi
             interval_cases i
             all_goals simp +zetaDelta [Ctxt.Valuation.singleton, Ctxt.Valuation.ofPair,
               Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
               LLVM.Ty.poison, toBitVecValue, limbNat, add_assoc, $hs,*]
             -- `wwl_slide` operands built with `Vector.replicate`/`append`
             -- index by computation rather than by a `simp` lemma.
             all_goals try rfl))

/-- `denote_vecbin hv` proves a goal `v = toBitVecValue 64 #v[…]` given the
`denote_step_all` hypothesis for a vector `llvm.shl`, `llvm.and`, `llvm.add`
or `llvm.mul`.

The op denotes as `Vector.ofFn fun i => binaryDenote .shl a[i] b[i]`, so the
sides are compared lanewise. Each lane unfolds through `LLVM.shl` to `shl?`,
whose `if op2 ≥ w` guard discharges because the shift amounts here are small;
`ofNat_shl*'` and the `BitVec.ofNat` fusion lemmas then keep the lane in
`BitVec.ofNat 64 (<ℕ expression>)` form.

Note `apply Vector.ext` rather than `ext`: the equation's type is
`⟦SLLVMTy.arith …⟧`, which `ext` will not match syntactically, but `apply`
unifies with `Vector.ext` up to defeq. -/
macro "denote_vecbin " h:term : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_denote_only
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta
               [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, LLVM.and, LLVM.and?,
                LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?, toBitVecValue, and_allOnes_64,
                ofNat_shl1', ofNat_shl9', ofNat_shl7', ofNat_mul24,
                ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
                ph, phRaw, LLVM.Ty.poison, add_assoc]
             all_goals try rfl))

/-- `denote_vpmadd52 hv with h…` proves a goal `v = toBitVecValue 64 #v[…]`
for an AVX-512 IFMA `vpmadd52l`/`vpmadd52h` instruction, lanewise as
`denote_vecbin`. An operand may be a block argument, so the valuation
constructors are in the simp set.

The lane truncates each operand mod `2^52`; the `with` list supplies the
operand bounds that make that truncation the identity, in the form
`Nat.mod_eq_of_lt h` for each bound `h`. `← BitVec.ofNat_add` folds the
addend — itself a `BitVec.ofNat` from the preceding instruction — into the
lane's single `ofNat`. -/
macro "denote_vpmadd52 " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_denote_only
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta
               [LLVM.Ty.vpmadd52, LLVM.Ty.vpmadd52Lane, toBitVecValue,
                Ctxt.Valuation.singleton, Ctxt.Valuation.ofPair,
                Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
                pl, phRaw, limbNat, Nat.mod_mod_of_dvd _ dvd52_64,
                ← BitVec.ofNat_add, Nat.mul_mod, Nat.mod_mod_of_dvd, $hs,*]))

end Firedancer.Avx512

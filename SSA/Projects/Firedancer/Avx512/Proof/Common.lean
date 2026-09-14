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

/-- `BitVec.toNat_ofNat` reintroduces a `% 2^64` that is always vacuous on a
lane read back out of a 64-bit vector. The default simp set cancels it; under
`simp only` it has to be named. -/
@[simp] theorem toNat_mod_two_pow_64 (v : BitVec 64) :
    v.toNat % 18446744073709551616 = v.toNat :=
  Nat.mod_eq_of_lt v.isLt

/-- `x &&& -1 = x`, for the `-1` a mask lane keeps under `simp only`. -/
theorem and_neg_one_64 (x : BitVec 64) : x &&& -1 = x := by
  rw [show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]

/-- `(0 : BitVec 64).toNat = 0`, for a zero lane read back under `simp only`. -/
theorem toNat_zero_64 : (0 : BitVec 64).toNat = 0 := rfl

/-- `add` of two literal `toBitVecValue` vectors, lanewise. Applied by `exact`, it
reads the lanes off the operands' `let`s without normalizing them. -/
theorem vec8_add (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote (InstCombine.MOp.BinaryOp.add {})
      (toBitVecValue 64 #v[a0, a1, a2, a3, a4, a5, a6, a7])[i.val]
      (toBitVecValue 64 #v[b0, b1, b2, b3, b4, b5, b6, b7])[i.val]) =
    toBitVecValue 64 #v[a0 + b0, a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5, a6 + b6, a7 + b7] := by
  apply Vector.ext; intro i hi
  interval_cases i <;> simp [InstCombine.binaryDenote, LLVM.add, LLVM.add?, toBitVecValue, BitVec.ofNat_add]

/-- `<<<` by a natural amount, as a multiplication inside `ofNat`. -/
theorem ofNat_shl_nat (a k : ℕ) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- A vector `shl` of a literal `toBitVecValue` by a constant lane `k < 64`, lanewise. -/
theorem vec8_shl_rep (a0 a1 a2 a3 a4 a5 a6 a7 k : ℕ) (hk : k < 64) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote (InstCombine.MOp.BinaryOp.shl {})
      (toBitVecValue 64 #v[a0, a1, a2, a3, a4, a5, a6, a7])[i.val]
      (toBitVecValue 64 (Vector.replicate 8 k))[i.val]) =
    toBitVecValue 64 #v[a0 * 2 ^ k, a1 * 2 ^ k, a2 * 2 ^ k, a3 * 2 ^ k, a4 * 2 ^ k,
      a5 * 2 ^ k, a6 * 2 ^ k, a7 * 2 ^ k] := by
  have hk' : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  have hkm : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
  have hlt : ¬ 64 ≤ k := by omega
  apply Vector.ext; intro i hi
  interval_cases i <;>
    simp [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, toBitVecValue, ofNat_shl, hk', ofNat_shl_nat, hkm, hlt]

/-- A vector `mul` of a literal `toBitVecValue` by a constant lane, lanewise. -/
theorem vec8_mul_rep (a0 a1 a2 a3 a4 a5 a6 a7 k : ℕ) :
    (Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote (InstCombine.MOp.BinaryOp.mul {})
      (toBitVecValue 64 #v[a0, a1, a2, a3, a4, a5, a6, a7])[i.val]
      (toBitVecValue 64 (Vector.replicate 8 k))[i.val]) =
    toBitVecValue 64 #v[a0 * k, a1 * k, a2 * k, a3 * k, a4 * k, a5 * k, a6 * k, a7 * k] := by
  apply Vector.ext; intro i hi
  interval_cases i <;> simp [InstCombine.binaryDenote, LLVM.mul, LLVM.mul?, toBitVecValue, BitVec.ofNat_mul]

open Lean Meta in
/-- The 8 lanes of a literal `toBitVecValue 64 #v[…]`, through `let`s. -/
private def vec8Lanes? (e : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let e ← if e.isFVar then pure ((← e.fvarId!.getDecl).value?.getD e) else pure e
  let_expr toBitVecValue _w _n v := e | return none
  let_expr Vector.mk _α _n arr _h := v | return none
  let_expr List.toArray _α l := arr | return none
  let some (_, xs) := l.listLit? | return none
  unless xs.length == 8 do return none
  return some xs.toArray

open Lean Meta in
/-- `k` of a `toBitVecValue 64 (Vector.replicate 8 k)`, through `let`s. -/
private def vec8Rep? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let e ← if e.isFVar then pure ((← e.fvarId!.getDecl).value?.getD e) else pure e
  let_expr toBitVecValue _w _n v := e | return none
  let_expr Vector.replicate _α _n k := v | return none
  return some k

open Lean Meta Elab Tactic in
/-- Close `Vector.ofFn (binaryDenote op A[·] B[·]) = C` by `vec8_add`, `vec8_shl_rep` or
`vec8_mul_rep`, chosen by `op` and the operands' shapes, with a capped defeq check. -/
elab "vec8_lemma" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := tgt.eq? | throwError "vec8_lemma: not an equation"
  let_expr Vector.ofFn _α _n f := lhs | throwError "vec8_lemma: not ofFn"
  let .lam _ _ body _ := f | throwError "vec8_lemma: not a lambda"
  let_expr InstCombine.binaryDenote _w op a b := body | throwError "vec8_lemma: not binaryDenote"
  unless a.isAppOfArity ``GetElem.getElem 8 && b.isAppOfArity ``GetElem.getElem 8 do
    throwError "vec8_lemma: operands"
  let A := a.getAppArgs[5]!
  let B := b.getAppArgs[5]!
  let some as ← vec8Lanes? A | throwError "vec8_lemma: first operand"
  let prf ← match op.getAppFn.constName? with
    | some ``InstCombine.MOp.BinaryOp.add => do
      let some bs ← vec8Lanes? B | throwError "vec8_lemma: second operand"
      pure (mkAppN (mkConst ``vec8_add) (as ++ bs))
    | some ``InstCombine.MOp.BinaryOp.shl => do
      let some k ← vec8Rep? B | throwError "vec8_lemma: shift amount"
      let hk ← mkDecideProof (← mkAppM ``LT.lt #[k, mkNatLit 64])
      pure (mkAppN (mkConst ``vec8_shl_rep) (as ++ #[k, hk]))
    | some ``InstCombine.MOp.BinaryOp.mul => do
      let some k ← vec8Rep? B | throwError "vec8_lemma: multiplier"
      pure (mkAppN (mkConst ``vec8_mul_rep) (as ++ #[k]))
    | _ => throwError "vec8_lemma: op"
  let ok ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 }) <|
    withCurrHeartbeats <| (do
      let ty ← inferType prf
      controlAt CoreM fun run => Core.tryCatchRuntimeEx (run (isDefEq ty tgt)) fun _ => run (pure false))
  unless ok do throwError "vec8_lemma: lanes differ"
  g.assign prf
  replaceMainGoal []

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

A whole-vector `add`/`shl`/`mul` of literal lanes closes by `vec8_lemma`. Otherwise each lane
tries a `simp only` without `ph`/`phRaw`/`add_assoc`, closed by `rfl`, before the normalizing set.

Note `apply Vector.ext` rather than `ext`: the equation's type is
`⟦SLLVMTy.arith …⟧`, which `ext` will not match syntactically, but `apply`
unifies with `Vector.ext` up to defeq. -/
macro "denote_vecbin " h:term : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_denote_only
             simp only [HVector.head]
             first
               | vec8_lemma
               | (apply Vector.ext
                  intro i hi
                  interval_cases i
                  all_goals first
                    | (simp +zetaDelta +decide only
                       [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, LLVM.and, LLVM.and?,
                        LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?, LLVM.Ty.poison,
                        toBitVecValue, and_allOnes_64, and_neg_one_64,
                        ofNat_shl1', ofNat_shl9', ofNat_shl7', ofNat_mul24,
                        ofNat_shl, ofNat_shl7, BitVec.toNat_ofNat,
                        ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
                        Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_eval,
                        Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons,
                        Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
                        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                        Array.getElem_replicate, Vector.getElem_replicate,
                        PoisonOr.value_bind, PoisonOr.poison_bind, PoisonOr.map_value,
                        PoisonOr.map_poison, PoisonOr.bind₂_value, PoisonOr.pure_def,
                        PoisonOr.mk_some, PoisonOr.mk_none, toNat_mod_two_pow_64,
                        Nat.reducePow, Nat.reduceMod, reduceIte,
                        Bool.false_eq_true, ite_false, ite_true, Nat.zero_add,
                        false_and, and_false, true_and, and_true]
                       try rfl
                       done)
                    | simp +zetaDelta
                       [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, LLVM.and, LLVM.and?,
                        LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?, toBitVecValue, and_allOnes_64,
                        ofNat_shl1', ofNat_shl9', ofNat_shl7', ofNat_mul24,
                        ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
                        ph, phRaw, LLVM.Ty.poison, add_assoc]
                  all_goals try rfl)))

/-- `denote_vpmadd52 hv with h…` proves a goal `v = toBitVecValue 64 #v[…]`
for an AVX-512 IFMA `vpmadd52l`/`vpmadd52h` instruction, lanewise as
`denote_vecbin`. An operand may be a block argument, so the valuation
constructors are in the simp set.

The lane truncates each operand mod `2^52`; the `with` list supplies the
operand bounds that make that truncation the identity, in the form
`Nat.mod_eq_of_lt h` for each bound `h`. `← BitVec.ofNat_add` folds the
addend — itself a `BitVec.ofNat` from the preceding instruction — into the
lane's single `ofNat`. As in `denote_vecbin`, each lane tries `quad_vpmadd52`'s
explicit set before the default one. -/
macro "denote_vpmadd52 " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_denote_only
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals first
               | (simp +zetaDelta only
                  [LLVM.Ty.vpmadd52, LLVM.Ty.vpmadd52Lane, toBitVecValue,
                   Ctxt.Valuation.singleton, Ctxt.Valuation.ofPair,
                   Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
                   Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_eval,
                   Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons,
                   Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
                   List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                   Array.getElem_replicate, Vector.getElem_replicate,
                   pl, phRaw, limbNat, toNat_zero_64, Nat.zero_mod, Nat.mul_zero,
                   Nat.zero_div, Nat.add_zero, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
                   Nat.mod_mod_of_dvd _ dvd52_64, toNat_mod_two_pow_64,
                   Nat.reducePow, Nat.reduceMod, reduceIte,
                   Bool.false_eq_true, ite_false, ite_true, Nat.zero_add,
                   false_and, and_false, true_and, and_true, $hs,*]
                  try rfl
                  done)
               | simp +zetaDelta
                  [LLVM.Ty.vpmadd52, LLVM.Ty.vpmadd52Lane, toBitVecValue,
                   Ctxt.Valuation.singleton, Ctxt.Valuation.ofPair,
                   Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
                   pl, phRaw, limbNat, Nat.mod_mod_of_dvd _ dvd52_64,
                   ← BitVec.ofNat_add, Nat.mul_mod, Nat.mod_mod_of_dvd, $hs,*]))

end Firedancer.Avx512

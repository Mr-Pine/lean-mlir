/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Spec.Quad

/-!
# Shared scaffolding for the `fd_r43x6_quad_*` proofs

The quad kernels take three or six `vector<8xi64>` block arguments and return
one 24-lane vector. This file fixes the valuations that feed them and the
readback of the 24-lane result.

Block arguments enter a `Ctxt` in *reverse* declaration order (`%arg0` is the
deepest variable), which is why `quadVal3`/`quadVal6` list their arguments
backwards.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The dialect type of an 8-lane 64-bit vector. -/
abbrev QTy : SLLVM.Ty := SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))
/-- The dialect type of the 24-lane result. -/
abbrev QTy24 : SLLVM.Ty := SLLVM.Ty.arith (.vector 24 (.bitvec (.concrete 64)))

/-- Valuation for a three-argument quad kernel (`fd_r43x6_quad_sqr_fast`).

Built as an explicit `Valuation.cons` chain rather than with
`Valuation.ofHVector`: the `@[simp]` lemma `Valuation.ofHVector_apply` rewrites
a lookup on an `ofHVector` into an `HVector` index, for which there are no
reduction lemmas in the per-opcode simp sets, so the operand of a `vpmadd52`
would get stuck. On a `cons` chain `Valuation.cons_zero` and
`Valuation.cons_eval` reduce the lookup all the way. -/
def quadVal3 (a b c : Vector (BitVec 64) 8) :
    Ctxt.Valuation (Ctxt.ofList [QTy, QTy, QTy]) :=
  c.map PoisonOr.value ::ᵥ b.map PoisonOr.value ::ᵥ a.map PoisonOr.value ::ᵥ
    Ctxt.Valuation.nil

/-- Valuation for a six-argument quad kernel (`fd_r43x6_quad_mul_fast`). -/
def quadVal6 (a b c d e f : Vector (BitVec 64) 8) :
    Ctxt.Valuation (Ctxt.ofList [QTy, QTy, QTy, QTy, QTy, QTy]) :=
  f.map PoisonOr.value ::ᵥ e.map PoisonOr.value ::ᵥ d.map PoisonOr.value ::ᵥ
  c.map PoisonOr.value ::ᵥ b.map PoisonOr.value ::ᵥ a.map PoisonOr.value ::ᵥ
    Ctxt.Valuation.nil

/-- `BitVec.toNat_ofNat` reintroduces a `% 2^64` that is always vacuous on a
lane read back out of a 64-bit vector. The default simp set cancels it; under
`simp only` it has to be named. -/
@[simp] theorem toNat_mod_two_pow_64 (v : BitVec 64) :
    v.toNat % 18446744073709551616 = v.toNat :=
  Nat.mod_eq_of_lt v.isLt

/-- `wwl_shl` applied to a *block argument*: the operand is a bare lane rather
than a `BitVec.ofNat`, so the `ofNat_shl*` family of `Proof/Common.lean` does
not match it. The shift amount comes in as a `BitVec`, hence `k.toNat`, which
`Nat.reduceMod` and `Nat.reducePow` finish off.

Deliberately *not* in `quad_vecbin`'s fixed simp set: it also matches
`BitVec.ofNat 64 x <<< k`, where it shadows the sharper `ofNat_shl` and routes
the operand through `.toNat`, leaving a vacuous `% 2^64` that only a bound on
`x` could discharge. The two instructions that shift a block argument name it
through `with` instead. -/
theorem shl_lane (v k : BitVec 64) :
    v <<< k = BitVec.ofNat 64 (2 ^ k.toNat * v.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

/-! ## A faster `vpmadd52` lane derivation

`denote_vpmadd52` of `Proof/Common.lean` finishes with a full `simp` -- the
whole default simp set -- once per lane, so eight times per instruction. On
these programs that one call is 3.18s of the 3.27s an instruction costs.

Replacing it with `simp only` over an explicit set brings an instruction to
0.83s. Two lemmas have to change for that to work:

* `Nat.mul_mod` is dropped. It loops under `simp only` (its right-hand side
  matches its own left-hand side), and it is not needed: the lane is
  `(u % 2^52) * (v % 2^52)`, and the `u47` operand bounds passed in through
  `with` rewrite each factor to itself, leaving `u * v` directly.
* `Nat.reducePow` has to be named, since `simp only` does not run the default
  simprocs and the operand bounds are stated over the literal `2^52`.

`Nat.mod_mod_of_dvd _ dvd52_64` stays, for the `% 2^64` a `BitVec.ofNat`
operand carries in under the `% 2^52`. -/

/-- As `denote_vpmadd52`, but with an explicit simp set. See above. -/
macro "quad_vpmadd52 " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta only
               [LLVM.Ty.vpmadd52, LLVM.Ty.vpmadd52Lane, toBitVecValue,
                Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_eval,
                Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons,
                Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
                List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                Array.getElem_replicate, Vector.getElem_replicate,
                quadLimb, vlane, pl, phRaw,
                ← BitVec.ofNat_add, BitVec.toNat_ofNat,
                Nat.mod_mod_of_dvd _ dvd52_64, toNat_mod_two_pow_64,
                Nat.reducePow, Nat.reduceMod, reduceIte,
                Bool.false_eq_true, ite_false, ite_true, Nat.zero_add,
                false_and, and_false, true_and, and_true, $hs,*]))

/-- As `denote_vecbin`, but taking extra simp lemmas through `with`.

The shared tactic has no `with` clause, so an instruction whose operand is a
block argument -- `two_x03 = wwl_shl( x03, 1 )` and friends -- cannot read that
argument out of the valuation. -/
macro "quad_vecbin " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta +decide only
               [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, LLVM.and, LLVM.and?,
                LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?, LLVM.Ty.poison,
                toBitVecValue, and_allOnes_64,
                ofNat_shl1', ofNat_shl9', ofNat_shl7', ofNat_mul24,
                ofNat_shl, ofNat_shl7, BitVec.toNat_ofNat,
                ← BitVec.ofNat_add, ← BitVec.ofNat_mul, ph, phRaw, add_assoc,
                Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_eval,
                Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons,
                Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
                List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                Array.getElem_replicate, Vector.getElem_replicate,
                PoisonOr.value_bind, PoisonOr.poison_bind, PoisonOr.map_value,
                PoisonOr.map_poison, PoisonOr.bind₂_value, PoisonOr.pure_def,
                PoisonOr.mk_some, PoisonOr.mk_none,
                quadLimb, vlane, toNat_mod_two_pow_64,
                Nat.reducePow, Nat.reduceMod, reduceIte,
                Bool.false_eq_true, ite_false, ite_true, Nat.zero_add,
                false_and, and_false, true_and, and_true, $hs,*]))

/-- `quad_vecbin` followed by `ring_nf`, for the `wwl_shl( ..., 9 )` steps only.

A `madd52hi` chain is summed *before* it is scaled, so such a lane arrives as
`(r₁ + r₂) * 512` where the specification has `ph .. + ph ..`. `ring_nf` closes
that gap, but it is expensive on the wide lanes further down the program -- the
`za + 152*zb` fold blows a 4M heartbeat budget with it -- so it is applied only
where the distribution is actually needed. -/
macro "quad_vecbin_ring " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| ((quad_vecbin $h with $hs,*); all_goals try ring_nf))

end Firedancer.Avx512

/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: the bulk of this file is the instruction-by-instruction derivation of
the 160 instructions of `fd_r43x6_sqr_fast`; unlike its `mul` counterpart it
has no generator, having been migrated from the earlier two-file
(`Denote/` + `Spec/`) layout at commit d4d7da2.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.MLIR.Poison
import SSA.Projects.Firedancer.Ed25519

/-!
# `fd_r43x6_sqr_fast` squares its input in `ZMod p`

Denoting the lifted SLLVM program and decoding the six output limbs yields the
square of the decoded input in `GF(2^255 - 19)`, within the widths the
`fd_r43x6.h` table promises.

The derivation runs at the ℕ level throughout: each of the 160 instructions is
reduced to a vector of `BitVec.ofNat 64` applied to an expression over `pl`
and `ph` (`Spec/Common.lean`), so `denote_fd_r43x6_sqr_fast` lands directly on
the specified `sqrVec x` and the ring correctness of `Spec/` applies without
an intermediate lane expression to transfer.

`fd_r43x6_sqr_fast` is *not* `fd_r43x6_mul_fast x x`: doubling of the
off-diagonal partial products happens *before* the multiplications rather than
after. The products formed are therefore `x i * x i` on the diagonal and
`(2 * x i) * x j` for `i < j` — twenty-one, against the thirty-six of a general
multiply.

## Hypotheses

`R43x6.Unreduced x` (u47) and `x[6] = x[7] = 0`, the contract stated in
`fd_r43x6.h`. The lane bounds it gives are what makes each `vpmadd52`
truncation the identity, and `x[7] = 0` is consumed at the shuffles, so no
product of the ignored lane is ever formed.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! The bound facts the per-opcode tactics need, bound once here rather than at
each of the instructions that needs them. `Lean.mkIdent` escapes macro hygiene
so these refer to the `have`s of the theorem below, which the generated body
names by convention. -/

local macro "sqr_shuffle " h:term : tactic =>
  `(tactic| denote_shuffle $h with $(Lean.mkIdent `h7):ident)

local macro "sqr_vpmadd52 " h:term : tactic =>
  `(tactic| denote_vpmadd52 $h with
      Nat.mod_eq_of_lt $(Lean.mkIdent `s0), Nat.mod_eq_of_lt $(Lean.mkIdent `s1),
      Nat.mod_eq_of_lt $(Lean.mkIdent `s2), Nat.mod_eq_of_lt $(Lean.mkIdent `s3),
      Nat.mod_eq_of_lt $(Lean.mkIdent `s4),
      Nat.mod_eq_of_lt $(Lean.mkIdent `t0), Nat.mod_eq_of_lt $(Lean.mkIdent `t1),
      Nat.mod_eq_of_lt $(Lean.mkIdent `t2), Nat.mod_eq_of_lt $(Lean.mkIdent `t3),
      Nat.mod_eq_of_lt $(Lean.mkIdent `t4), Nat.mod_eq_of_lt $(Lean.mkIdent `t5))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **Limb derivation** for `fd_r43x6_sqr_fast`: on an unreduced input with
lane 7 zero, the denotation *is* the specified limb vector `sqrVec x` — every
one of the 160 instructions carried through at the ℕ level. -/
theorem denote_fd_r43x6_sqr_fast (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) :
    fd_r43x6_sqr_fast.denote
        (Ctxt.Valuation.singleton (x.map PoisonOr.value)) =
      ([(sqrVec x).map PoisonOr.value]ₕ :
        HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))]) := by
  have u0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0 (by omega)
  have u1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1 (by omega)
  have u2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2 (by omega)
  have u3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3 (by omega)
  have u4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4 (by omega)
  have u5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5 (by omega)
  -- Bounds in literal form: simp's `Nat.reducePow` normalises `2^52` to it.
  have s0 : 2 * x[0].toNat < 4503599627370496 := by omega
  have s1 : 2 * x[1].toNat < 4503599627370496 := by omega
  have s2 : 2 * x[2].toNat < 4503599627370496 := by omega
  have s3 : 2 * x[3].toNat < 4503599627370496 := by omega
  have s4 : 2 * x[4].toNat < 4503599627370496 := by omega
  have t0 : x[0].toNat < 4503599627370496 := by omega
  have t1 : x[1].toNat < 4503599627370496 := by omega
  have t2 : x[2].toNat < 4503599627370496 := by omega
  have t3 : x[3].toNat < 4503599627370496 := by omega
  have t4 : x[4].toNat < 4503599627370496 := by omega
  have t5 : x[5].toNat < 4503599627370496 := by omega
  unfold fd_r43x6_sqr_fast
  denote_step_all v 3
  let x0Shifts := toBitVecValue 64 #v[0, 1, 1, 1, 1, 1, 0, 1]
  let x2Shifts := toBitVecValue 64 #v[0, 1, 0, 1, 1, 1, 1, 1]
  let x4Shifts := toBitVecValue 64 #v[1, 1, 0, 1, 0, 1, 1, 1]
  have v1Value : v1 = x0Shifts := by denote_dense hv1
  have v2Value : v2 = x2Shifts := by denote_dense hv2
  have v3Value : v3 = x4Shifts := by denote_dense hv3
  subst v1Value v2Value v3Value
  clear hv0 hv1 hv2 hv3

  let zeroBVP : PoisonOr (BitVec 64) := .value 0
  let neg1BVP : PoisonOr (BitVec 64) := .value (-1)

  denote_step_all v 4

  have v4Zero : v4 = zeroBVP := by
    simp only [hv4, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head]
    rfl
  subst v4Zero
  clear hv4


  let mask1Not : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[zeroBVP, zeroBVP,
       neg1BVP, neg1BVP,
       neg1BVP, neg1BVP,
       neg1BVP, neg1BVP]
  let mask1With2Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP,
       zeroBVP, zeroBVP,
       zeroBVP, zeroBVP,
       .poison, .poison]
  let mask1With3Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP,
       zeroBVP, zeroBVP,
       zeroBVP,
       .poison, .poison, .poison]

  let mask2Not : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[zeroBVP, neg1BVP,
       zeroBVP, neg1BVP,
       neg1BVP, neg1BVP,
       neg1BVP, neg1BVP]
  let mask2With2Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, zeroBVP,
       neg1BVP, zeroBVP,
       zeroBVP, zeroBVP,
       .poison, .poison]
  let mask2With3Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, zeroBVP,
       neg1BVP, zeroBVP,
       zeroBVP,
       .poison, .poison, .poison]

  denote_step_all v 8
  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)
  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)
  have v5Zero: v5 = zeroVec := by denote_dense hv5
  have v6Nine: v6 = nineVec := by denote_dense hv6
  subst v5Zero v6Nine
  denote_clear v 5 6

  have v7Mask1Not: v7 = mask1Not := by denote_dense hv7
  have v8Mask1Not: v8 = mask2Not := by denote_dense hv8
  subst v7Mask1Not v8Mask1Not
  denote_clear v 7 8

  denote_step_all v 27

  have v9Poison : v9 = PoisonOr.poison := by
    simp only [hv9]
    simp_peephole
    rfl
  have v10Neg1 : v10 = neg1BVP := by
    simp only [hv10, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head]
    rfl
  subst v10Neg1 v9Poison
  clear hv10 hv9

  have v27Value : v27 = mask1With2Poison := by
    -- Evaluate each instruction of the chain on its own (cheap), then expand
    -- the chain into the goal; inlining first and evaluating after does not
    -- scale.
    denote_eval v 4 27
    denote_expand v 4 27
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v27Value
  clear hv27
  denote_clear v 11 26

  denote_step_all v 44

  have v44Value: v44 = mask2With2Poison := by
    denote_eval v 28 44
    denote_expand v 28 44
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v44Value
  denote_clear v 28 44

  denote_step_all v 61
  have v61Value : v61 = mask1With3Poison := by
    denote_eval v 45 61
    denote_expand v 45 61
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v61Value
  denote_clear v 45 61

  denote_step_all v 78
  have v78Value : v78 = mask2With3Poison := by
    denote_eval v 62 78
    denote_expand v 62 78
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v78Value
  denote_clear v 62 78

  let p7_zero1 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 7 PoisonOr.poison).append (#v[PoisonOr.value (BitVec.zero 64)])
  let zero5_p3 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 5 (.value (BitVec.zero 64))).append (Vector.replicate 3 .poison)

  denote_step_all v 95
  have v95Value : v95 = p7_zero1 := by
    denote_eval v 79 95
    denote_expand v 79 95
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  denote_step_all v 112
  have v112Value : v112 = zero5_p3 := by
    denote_eval v 96 112
    denote_expand v 96 112
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v95Value v112Value
  denote_clear v 79 112

  -- Written out rather than `replicate/append`: `and_allOnes_64` can only fire
  -- on a lane that `simp` can actually index out of the mask.
  let zaMask : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, zeroBVP, zeroBVP]
  let dense7 := toBitVecValue 64 (Vector.replicate 8 7)
  let dense24 := toBitVecValue 64 (Vector.replicate 8 24)
  denote_step_all v 115
  have v113Value : v113 = zaMask := by denote_dense hv113
  have v114Value : v114 = dense7 := by denote_dense hv114
  have v115Value : v115 = dense24 := by denote_dense hv115
  subst v113Value v114Value v115Value
  denote_clear v 113 115

  denote_step_all v 121
  -- Name the lanes once, so the 260-odd uses below do not each re-elaborate
  -- an `x[i]` bounds proof.
  let x_0 : ℕ := limbNat x 0
  let x_1 : ℕ := limbNat x 1
  let x_2 : ℕ := limbNat x 2
  let x_3 : ℕ := limbNat x 3
  let x_4 : ℕ := limbNat x 4
  let x_5 : ℕ := limbNat x 5

  let x0 := toBitVecValue 64 #v[x_0, x_0, x_0, x_0, x_0, x_0, x_3, x_3]
  let x1 := toBitVecValue 64 #v[x_0, x_1, x_2, x_3, x_4, x_5, x_3, x_4]
  let x2 := toBitVecValue 64 #v[x_4, x_4, x_1, x_1, x_1, x_1, x_1, 0]
  let x3 := toBitVecValue 64 #v[x_4, x_5, x_1, x_2, x_3, x_4, x_5, 0]
  let x4 := toBitVecValue 64 #v[x_3, 0, x_5, 0, x_2, x_2, x_2, x_2]
  let x5 := toBitVecValue 64 #v[x_5, 0, x_5, 0, x_2, x_3, x_4, x_5]

  have v116Value : v116 = x0 := by sqr_shuffle hv116
  have v117Value : v117 = x1 := by sqr_shuffle hv117
  have v118Value : v118 = x2 := by sqr_shuffle hv118
  have v119Value : v119 = x3 := by sqr_shuffle hv119
  have v120Value : v120 = x4 := by sqr_shuffle hv120
  have v121Value : v121 = x5 := by sqr_shuffle hv121
  subst v116Value v117Value v118Value v119Value v120Value v121Value
  denote_clear v 116 121

  denote_step_all v 124
  -- `%122`–`%124` shift the shuffled lanes by the `x*Shifts` constants.
  let x0 := toBitVecValue 64 #v[x_0, 2 * x_0, 2 * x_0, 2 * x_0, 2 * x_0, 2 * x_0, x_3, 2 * x_3]
  let x2 := toBitVecValue 64 #v[x_4, 2 * x_4, x_1, 2 * x_1, 2 * x_1, 2 * x_1, 2 * x_1, 0]
  let x4 := toBitVecValue 64 #v[2 * x_3, 0, x_5, 0, x_2, 2 * x_2, 2 * x_2, 2 * x_2]

  have v122Value : v122 = x0 := by denote_vecbin hv122
  have v123Value : v123 = x2 := by denote_vecbin hv123
  have v124Value : v124 = x4 := by denote_vecbin hv124

  subst v122Value v123Value v124Value
  denote_clear v 116 124

  denote_step_all v 137

  -- `%125`-`%127` = `p0l`, `p1l`, `p2l`: `wwl_madd52lo( zero, x_, x_ )`.
  let p0l := toBitVecValue 64 #v[pl (x_0) (x_0), pl (2 * x_0) (x_1), pl (2 * x_0) (x_2), pl (2 * x_0) (x_3), pl (2 * x_0) (x_4), pl (2 * x_0) (x_5), pl (x_3) (x_3), pl (2 * x_3) (x_4)]
  let p1l := toBitVecValue 64 #v[pl (x_4) (x_4), pl (2 * x_4) (x_5), pl (x_1) (x_1), pl (2 * x_1) (x_2), pl (2 * x_1) (x_3), pl (2 * x_1) (x_4), pl (2 * x_1) (x_5), 0]
  let p2l := toBitVecValue 64 #v[pl (2 * x_3) (x_5), 0, pl (x_5) (x_5), 0, pl (x_2) (x_2), pl (2 * x_2) (x_3), pl (2 * x_2) (x_4), pl (2 * x_2) (x_5)]
  have v125Value : v125 = p0l := by sqr_vpmadd52 hv125
  have v126Value : v126 = p1l := by sqr_vpmadd52 hv126
  have v127Value : v127 = p2l := by sqr_vpmadd52 hv127

  -- `%129`, `%131`, `%133` = `p0h`, `p1h`, `p2h`: `wwl_shl( wwl_madd52hi( zero, .. ), 9 )`.
  -- The unshifted `%128`/`%130`/`%132` are unnamed in the source.
  let p0hRaw := toBitVecValue 64 #v[phRaw (x_0) (x_0), phRaw (2 * x_0) (x_1), phRaw (2 * x_0) (x_2), phRaw (2 * x_0) (x_3), phRaw (2 * x_0) (x_4), phRaw (2 * x_0) (x_5), phRaw (x_3) (x_3), phRaw (2 * x_3) (x_4)]
  let p1hRaw := toBitVecValue 64 #v[phRaw (x_4) (x_4), phRaw (2 * x_4) (x_5), phRaw (x_1) (x_1), phRaw (2 * x_1) (x_2), phRaw (2 * x_1) (x_3), phRaw (2 * x_1) (x_4), phRaw (2 * x_1) (x_5), 0]
  let p2hRaw := toBitVecValue 64 #v[phRaw (2 * x_3) (x_5), 0, phRaw (x_5) (x_5), 0, phRaw (x_2) (x_2), phRaw (2 * x_2) (x_3), phRaw (2 * x_2) (x_4), phRaw (2 * x_2) (x_5)]
  have v128Value : v128 = p0hRaw := by sqr_vpmadd52 hv128
  have v130Value : v130 = p1hRaw := by sqr_vpmadd52 hv130
  have v132Value : v132 = p2hRaw := by sqr_vpmadd52 hv132
  subst v128Value v130Value v132Value

  let p0h := toBitVecValue 64 #v[ph (x_0) (x_0), ph (2 * x_0) (x_1), ph (2 * x_0) (x_2), ph (2 * x_0) (x_3), ph (2 * x_0) (x_4), ph (2 * x_0) (x_5), ph (x_3) (x_3), ph (2 * x_3) (x_4)]
  let p1h := toBitVecValue 64 #v[ph (x_4) (x_4), ph (2 * x_4) (x_5), ph (x_1) (x_1), ph (2 * x_1) (x_2), ph (2 * x_1) (x_3), ph (2 * x_1) (x_4), ph (2 * x_1) (x_5), 0]
  let p2h := toBitVecValue 64 #v[ph (2 * x_3) (x_5), 0, ph (x_5) (x_5), 0, ph (x_2) (x_2), ph (2 * x_2) (x_3), ph (2 * x_2) (x_4), ph (2 * x_2) (x_5)]
  have v129Value : v129 = p0h := by denote_vecbin hv129
  have v131Value : v131 = p1h := by denote_vecbin hv131
  have v133Value : v133 = p2h := by denote_vecbin hv133

  -- `%134`-`%137`: the `wwl_andnot( mask1/mask2, p.. )` terms -- the lanes
  -- belonging to the *low* word. Unnamed in the source, where they appear
  -- inline in `zll` and `zlh`.
  subst v126Value v127Value v131Value v133Value
  let p1lLow := toBitVecValue 64 #v[0, 0, pl (x_1) (x_1), pl (2 * x_1) (x_2), pl (2 * x_1) (x_3), pl (2 * x_1) (x_4), pl (2 * x_1) (x_5), 0]
  let p2lLow := toBitVecValue 64 #v[0, 0, 0, 0, pl (x_2) (x_2), pl (2 * x_2) (x_3), pl (2 * x_2) (x_4), pl (2 * x_2) (x_5)]
  let p1hLow := toBitVecValue 64 #v[0, 0, ph (x_1) (x_1), ph (2 * x_1) (x_2), ph (2 * x_1) (x_3), ph (2 * x_1) (x_4), ph (2 * x_1) (x_5), 0]
  let p2hLow := toBitVecValue 64 #v[0, 0, 0, 0, ph (x_2) (x_2), ph (2 * x_2) (x_3), ph (2 * x_2) (x_4), ph (2 * x_2) (x_5)]
  have v134Value : v134 = p1lLow := by denote_vecbin hv134
  have v135Value : v135 = p2lLow := by denote_vecbin hv135
  have v136Value : v136 = p1hLow := by denote_vecbin hv136
  have v137Value : v137 = p2hLow := by denote_vecbin hv137

  subst v125Value v129Value v134Value v135Value v136Value v137Value
  denote_clear v 125 137

  denote_step_all v 147

  -- `%138`/`%146` are unnamed in the source: LLVM reassociated
  -- `wwl_add( p0_, wwl_add( a, b ) )` into `(a + p0_) + b`.
  -- `%139` = `zlh`, `%147` = `zll`.
  let zlhPart := toBitVecValue 64 #v[0 + ph (x_0) (x_0), 0 + ph (2 * x_0) (x_1), ph (x_1) (x_1) + ph (2 * x_0) (x_2), ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3), ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4), ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5), ph (2 * x_1) (x_5) + ph (x_3) (x_3), 0 + ph (2 * x_3) (x_4)]
  let zlh := toBitVecValue 64 #v[(0 + ph (x_0) (x_0)) + 0, (0 + ph (2 * x_0) (x_1)) + 0, (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4), (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)]
  have v138Value : v138 = zlhPart := by denote_vecbin hv138
  subst v138Value
  have v139Value : v139 = zlh := by denote_vecbin hv139

  let zllPart := toBitVecValue 64 #v[0 + pl (x_0) (x_0), 0 + pl (2 * x_0) (x_1), pl (x_1) (x_1) + pl (2 * x_0) (x_2), pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3), pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4), pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5), pl (2 * x_1) (x_5) + pl (x_3) (x_3), 0 + pl (2 * x_3) (x_4)]
  let zll := toBitVecValue 64 #v[(0 + pl (x_0) (x_0)) + 0, (0 + pl (2 * x_0) (x_1)) + 0, (pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0, (pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0, (pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2), (pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3), (pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4), (0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5)]
  have v146Value : v146 = zllPart := by denote_vecbin hv146
  subst v146Value
  have v147Value : v147 = zll := by denote_vecbin hv147

  denote_step_all v 151

  -- `%140`-`%143`: the `wwl_and( mask1/mask2, p.. )` terms -- the lanes belonging
  -- to the *high* word. The masks are the poisoned `%27`/`%44`/`%61`/`%78`, so
  -- these carry poison lanes and are not of the `.map PoisonOr.value` shape.
  let p1lHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (x_4) (x_4))), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  let p2lHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (pl (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  let p1hHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (ph (x_4) (x_4))), .value (BitVec.ofNat 64 (ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison, .poison]
  let p2hHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (ph (2 * x_3) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison, .poison]
  have v140Value : v140 = p1lHigh := by denote_vecbin hv140
  have v141Value : v141 = p2lHigh := by denote_vecbin hv141
  have v142Value : v142 = p1hHigh := by denote_vecbin hv142
  have v143Value : v143 = p2hHigh := by denote_vecbin hv143
  subst v140Value v141Value v142Value v143Value

  -- `%144` = `zhh`, `%151` = `zhl`.
  let zhh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (ph (2 * x_3) (x_5) + ph (x_4) (x_4))), .value (BitVec.ofNat 64 (ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison, .poison]
  let zhl : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5) + pl (x_4) (x_4))), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (pl (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v144Value : v144 = zhh := by denote_vecbin hv144
  have v151Value : v151 = zhl := by denote_vecbin hv151

  subst v139Value v147Value v144Value v151Value
  denote_step_all v 155

  -- `%145`, `%149`, `%150` are `wwl_slide`: `shufflevector` whose mask reaches
  -- into the *second* operand.
  let zlhSlide := toBitVecValue 64 #v[0, (0 + ph (x_0) (x_0)) + 0, (0 + ph (2 * x_0) (x_1)) + 0, (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)]
  have v145Value : v145 = zlhSlide := by sqr_shuffle hv145
  subst v145Value

  -- `%148` = `zl`.
  let zl := toBitVecValue 64 #v[(0 + pl (x_0) (x_0)) + 0 + 0, (0 + pl (2 * x_0) (x_1)) + 0 + (0 + ph (x_0) (x_0)) + 0, (pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0 + (0 + ph (2 * x_0) (x_1)) + 0, (pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0 + (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2) + (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3) + (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), (pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)]
  have v148Value : v148 = zl := by denote_vecbin hv148
  subst v148Value

  let zhhSlide : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (ph (2 * x_3) (x_5) + ph (x_4) (x_4))), .value (BitVec.ofNat 64 (ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  let zlhSlide7 : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 ((0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v149Value : v149 = zhhSlide := by sqr_shuffle hv149
  have v150Value : v150 = zlhSlide7 := by sqr_shuffle hv150
  subst v149Value v150Value

  -- `%153` = `zh`.
  let zhPart : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0)), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4))), .value (BitVec.ofNat 64 (pl (x_5) (x_5) + ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (0 + ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0 + 0)), .value (BitVec.ofNat 64 (0 + 0)), .poison, .poison]
  let zh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5))), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0)), .value (BitVec.ofNat 64 (pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0)), .value (BitVec.ofNat 64 (0 + ph (x_5) (x_5) + 0)), .value (BitVec.ofNat 64 (0 + 0 + 0)), .value (BitVec.ofNat 64 (0 + 0 + 0)), .poison, .poison]
  have v152Value : v152 = zhPart := by denote_vecbin hv152
  subst v152Value
  have v153Value : v153 = zh := by denote_vecbin hv153
  subst v153Value

  -- `%154` = `za`, `%155` = `zb`.
  let za := toBitVecValue 64 #v[(0 + pl (x_0) (x_0)) + 0 + 0, (0 + pl (2 * x_0) (x_1)) + 0 + (0 + ph (x_0) (x_0)) + 0, (pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0 + (0 + ph (2 * x_0) (x_1)) + 0, (pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0 + (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2) + (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3) + (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), 0, 0]
  let zb := toBitVecValue 64 #v[(pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4), pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5), pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0, pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0, 0 + ph (x_5) (x_5) + 0, 0 + 0 + 0, 0 + 0 + 0]
  have v154Value : v154 = za := by denote_vecbin hv154
  have v155Value : v155 = zb := by sqr_shuffle hv155

  subst v154Value v155Value
  denote_step_all v 159

  -- `%156`-`%159`: the final fold.
  let zbShl7 := toBitVecValue 64 #v[((pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3)) * 128, ((0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)) * 128, (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)) * 128, (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0) * 128, (pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0) * 128, (0 + ph (x_5) (x_5) + 0) * 128, (0 + 0 + 0) * 128, (0 + 0 + 0) * 128]
  have v156Value : v156 = zbShl7 := by denote_vecbin hv156
  subst v156Value
  let zbShl7Za := toBitVecValue 64 #v[(((pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3)) * 128) + ((0 + pl (x_0) (x_0)) + 0 + 0), (((0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)) * 128) + ((0 + pl (2 * x_0) (x_1)) + 0 + (0 + ph (x_0) (x_0)) + 0), ((pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)) * 128) + ((pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0 + (0 + ph (2 * x_0) (x_1)) + 0), ((pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0) * 128) + ((pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0 + (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0), ((pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0) * 128) + ((pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2) + (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0), ((0 + ph (x_5) (x_5) + 0) * 128) + ((pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3) + (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2)), ((0 + 0 + 0) * 128) + (0), ((0 + 0 + 0) * 128) + (0)]
  let zbMul24 := toBitVecValue 64 #v[((pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3)) * 24, ((0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)) * 24, (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)) * 24, (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0) * 24, (pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0) * 24, (0 + ph (x_5) (x_5) + 0) * 24, (0 + 0 + 0) * 24, (0 + 0 + 0) * 24]
  have v157Value : v157 = zbShl7Za := by denote_vecbin hv157
  have v158Value : v158 = zbMul24 := by denote_vecbin hv158
  subst v157Value v158Value
  -- `%159`: the final add, against `sqrVec` directly; the lane sums are
  -- already ℕ-level, so only `sqLimb` unfolding and `ring` remain.
  have v159Value : v159 = (sqrVec x).map PoisonOr.value := by
    simp only [sqrVec, limbVec]
    denote_vecbin hv159
    all_goals try congr 1
    all_goals try simp only [sqLimb, sqCol, limbNat, ph, pl]
    all_goals try ring_nf
  subst v159Value
  simp_peephole

abbrev sqrValue (x: Vector (BitVec 64) 8) := (fd_r43x6_sqr_fast.denote
          (Ctxt.Valuation.singleton (x.map PoisonOr.value))).head.getValues

abbrev sqrIsSqr (x: Vector (BitVec 64) 8) := (fun l => (R43x6.decode' l : ZMod p)) <$> sqrValue x
      = .value ((R43x6.decode' x : ZMod p)^2)

private def output_bounds_u44_u61 (x: Vector (BitVec 64) 8) := R43x6.U44 x → R43x6.U61 (sqrValue x).getValue
private def output_bounds_u45_u61 (x: Vector (BitVec 64) 8) := R43x6.U45 x → R43x6.U61 (sqrValue x).getValue
private def output_bounds_u46_u62 (x: Vector (BitVec 64) 8) := R43x6.U46 x → R43x6.U62 (sqrValue x).getValue
private def output_bounds_u47_u62 (x: Vector (BitVec 64) 8) := R43x6.U47 x → R43x6.U62 (sqrValue x).getValue

set_option maxHeartbeats 1000000 in
private theorem sqrIsSqrThm (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) :
    sqrIsSqr x := by
  have b0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0 (by omega)
  have b1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1 (by omega)
  have b2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2 (by omega)
  have b3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3 (by omega)
  have b4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4 (by omega)
  have b5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5 (by omega)
  have hbnd : ∀ i < 6, limbNat x i < 2^47 := by
    intro i hi
    interval_cases i <;> simpa [limbNat] using ‹_›
  -- 1. denotation to lanes to specified limbs; the poison layer collapses
  rw [sqrIsSqr, sqrValue, denote_fd_r43x6_sqr_fast x hx h7]
  simp only [HVector.head, Vector.getValues_map_value, PoisonOr.map_value,
    PoisonOr.value_inj]
  -- 2. decode both sides into explicit sums
  have hx8 : x = #v[x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]] := by
    apply Vector.ext; intro i hi; interval_cases i <;> rfl
  have hdx : R43x6.decode' x = (limbNat x 0 : Int) + 2^43 * limbNat x 1
      + 2^86 * limbNat x 2 + 2^129 * limbNat x 3 + 2^172 * limbNat x 4
      + 2^215 * limbNat x 5 := by
    conv_lhs => rw [hx8]
    rw [decode'_lit, toInt_of_lt b0, toInt_of_lt b1, toInt_of_lt b2,
      toInt_of_lt b3, toInt_of_lt b4, toInt_of_lt b5]
    simp [limbNat]
  rw [sqrVec, decode'_limbVec _ (sqLimb_lt_two_pow_63 _ hbnd), hdx,
    show ((limbNat x 0 : Int) + 2^43 * limbNat x 1 + 2^86 * limbNat x 2
        + 2^129 * limbNat x 3 + 2^172 * limbNat x 4 + 2^215 * limbNat x 5)
      = ((pack (limbNat x) : ℕ) : Int) from by simp [pack]; try ring]
  -- 3. both sides are now casts of `pack`, so `pack_sqLimb_zmod` applies
  push_cast
  exact pack_sqLimb_zmod (limbNat x)

/-! ## Output bounds

The four rows of the `fd_r43x6.h` table, each `sqLimb_lt_u4x` transported
through the denotation: output lane `k < 6` is the specified limb, lanes 6
and 7 are zero, and none is read back as negative. -/

/-- The program's result, with the poison layer discharged. -/
private theorem sqrValue_eq (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) :
    sqrValue x = .value (sqrVec x) := by
  rw [sqrValue, denote_fd_r43x6_sqr_fast x hx h7]
  simp only [HVector.head, Vector.getValues_map_value]

/-- Two-sided lane bounds from a ceiling `N` on the ℕ-level limbs. -/
private theorem output_bounds_of (x : Vector (BitVec 64) 8) (N : ℕ) (hN : N ≤ 2^62)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0)
    (hb : ∀ k < 6, sqLimb (limbNat x) k < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (sqrValue x).getValue
      ∧ R43x6.BoundedLower 0 (sqrValue x).getValue := by
  have hv : (sqrValue x).getValue = sqrVec x := by rw [sqrValue_eq x hx h7]; rfl
  rw [hv, sqrVec]
  exact limbVec_bounds _ N (by omega) hb

private theorem output_u44 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u44_u61 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^61 := fun k hk =>
    sqLimb_lt_u44 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 44 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^61) (by omega) hx h7 hb

private theorem output_u45 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u45_u61 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^61 := fun k hk =>
    sqLimb_lt_u45 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 45 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^61) (by omega) hx h7 hb

private theorem output_u46 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u46_u62 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^62 := fun k hk =>
    sqLimb_lt_u46 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 46 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^62) (by omega) hx h7 hb

private theorem output_u47 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u47_u62 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^62 := fun k hk =>
    sqLimb_lt_u47 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 47 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^62) (by omega) hx h7 hb

/-- **Specification of `fd_r43x6_sqr_fast`**: on an unreduced input whose two
high lanes are zero, the six output limbs decode to the square of the decoded
input in `GF(2^255 - 19)`, and the four input/output width guarantees of
`fd_r43x6.h` hold.

`_h6` is the other half of the `fd_r43x6.h` contract ("lanes 6 and 7 of x are
zero"); it is kept in the statement for fidelity to that contract, though the
derivation turns out not to need it -- lane 6 of `x` reaches no product. -/
theorem spec_fd_r43x6_sqr_fast (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (_h6 : x[6] = 0) (h7 : x[7] = 0) :
    sqrIsSqr x ∧ output_bounds_u44_u61 x ∧ output_bounds_u45_u61 x
      ∧ output_bounds_u46_u62 x ∧ output_bounds_u47_u62 x :=
  ⟨sqrIsSqrThm x hx h7, output_u44 x hx h7, output_u45 x hx h7,
    output_u46 x hx h7, output_u47 x hx h7⟩

end Firedancer.Avx512

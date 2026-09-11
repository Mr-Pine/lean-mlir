/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: the bulk of this file is the instruction-by-instruction derivation of
the 120 instructions of `fd_r43x6_sqr_fast`; unlike its `mul` counterpart it
has no generator, having been migrated from the earlier two-file
(`Denote/` + `Spec/`) layout at commit d4d7da2.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.MLIR.Poison
import SSA.Projects.Firedancer.Ed25519

/-!
# `fd_r43x6_sqr_fast` squares its input in `ZMod p`

Denoting the lifted SLLVM program and decoding the six output limbs yields the
square of the decoded input in `GF(2^255 - 19)`, within the widths the
`fd_r43x6.h` table promises.

The derivation runs at the ℕ level throughout: each of the 120 instructions is
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
one of the 120 instructions carried through at the ℕ level. -/
theorem denote_fd_r43x6_sqr_fast (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) :
    fd_r43x6_sqr_fast.denote
        (Ctxt.Valuation.singleton (x.map PoisonOr.value)) =
      ([(sqrVec x).map PoisonOr.value]ₕ :
        HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))]) := by
  have u0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0
  have u1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1
  have u2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2
  have u3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3
  have u4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4
  have u5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5
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
  denote_step_reduce v 75 [LLVM.const?, LLVM.Ty.poison] fold
  let zeroBVP : PoisonOr (BitVec 64) := .value 0
  let neg1BVP : PoisonOr (BitVec 64) := .value (-1)

  -- `%0`-`%2`, `%12`-`%15`, `%17`-`%19`: the dense constants.
  let x0Shifts := toBitVecValue 64 #v[0, 1, 1, 1, 1, 1, 0, 1]
  let x2Shifts := toBitVecValue 64 #v[0, 1, 0, 1, 1, 1, 1, 1]
  let x4Shifts := toBitVecValue 64 #v[1, 1, 0, 1, 0, 1, 1, 1]
  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)
  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)
  let mask1Not : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[zeroBVP, zeroBVP,
       neg1BVP, neg1BVP,
       neg1BVP, neg1BVP,
       neg1BVP, neg1BVP]
  let mask2Not : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[zeroBVP, neg1BVP,
       zeroBVP, neg1BVP,
       neg1BVP, neg1BVP,
       neg1BVP, neg1BVP]
  -- Written out rather than `replicate/append`: `and_allOnes_64` can only fire
  -- on a lane that `simp` can actually index out of the mask.
  let zaMask : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, zeroBVP, zeroBVP]
  let dense7 := toBitVecValue 64 (Vector.replicate 8 7)
  let dense24 := toBitVecValue 64 (Vector.replicate 8 24)
  have v0Value : v0 = dense24 := by denote_dense hv0
  have v1Value : v1 = dense7 := by denote_dense hv1
  have v2Value : v2 = zaMask := by denote_dense hv2
  have v12Value : v12 = mask2Not := by denote_dense hv12
  have v13Value : v13 = mask1Not := by denote_dense hv13
  have v14Value : v14 = nineVec := by denote_dense hv14
  have v15Value : v15 = zeroVec := by denote_dense hv15
  have v17Value : v17 = x4Shifts := by denote_dense hv17
  have v18Value : v18 = x2Shifts := by denote_dense hv18
  have v19Value : v19 = x0Shifts := by denote_dense hv19

  -- `%30`, `%39`, …, `%75`: the `insertelement` chains, with poison lanes.
  let mask1With2Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP,
       zeroBVP, zeroBVP,
       zeroBVP, zeroBVP,
       .poison, .poison]
  let mask2With2Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, zeroBVP,
       neg1BVP, zeroBVP,
       zeroBVP, zeroBVP,
       .poison, .poison]
  let mask1With3Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP,
       zeroBVP, zeroBVP,
       zeroBVP,
       .poison, .poison, .poison]
  let mask2With3Poison : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, zeroBVP,
       neg1BVP, zeroBVP,
       zeroBVP,
       .poison, .poison, .poison]
  let p7_zero1 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 7 PoisonOr.poison).append (#v[PoisonOr.value (BitVec.zero 64)])
  let zero5_p3 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 5 (.value (BitVec.zero 64))).append (Vector.replicate 3 .poison)
  have v30Value : v30 = mask1With2Poison := by
    simp only [hv30]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, mask1With2Poison] <;> rfl
  have v39Value : v39 = mask2With2Poison := by
    simp only [hv39]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, mask2With2Poison] <;> rfl
  have v48Value : v48 = mask1With3Poison := by
    simp only [hv48]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, mask1With3Poison] <;> rfl
  have v57Value : v57 = mask2With3Poison := by
    simp only [hv57]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, mask2With3Poison] <;> rfl
  have v66Value : v66 = p7_zero1 := by
    simp only [hv66]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, p7_zero1] <;> rfl
  have v75Value : v75 = zero5_p3 := by
    simp only [hv75]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, zero5_p3] <;> rfl
  subst v0Value v1Value v2Value v12Value v13Value v14Value v15Value v17Value v18Value v19Value
  subst v30Value v39Value v48Value v57Value v66Value v75Value
  denote_clear v 0 75

  denote_step_all v 81
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

  have v76Value : v76 = x0 := by sqr_shuffle hv76
  have v77Value : v77 = x1 := by sqr_shuffle hv77
  have v78Value : v78 = x2 := by sqr_shuffle hv78
  have v79Value : v79 = x3 := by sqr_shuffle hv79
  have v80Value : v80 = x4 := by sqr_shuffle hv80
  have v81Value : v81 = x5 := by sqr_shuffle hv81
  subst v76Value v77Value v78Value v79Value v80Value v81Value
  denote_clear v 76 81

  denote_step_all v 84
  -- `%82`–`%84` shift the shuffled lanes by the `x*Shifts` constants.
  let x0 := toBitVecValue 64 #v[x_0, 2 * x_0, 2 * x_0, 2 * x_0, 2 * x_0, 2 * x_0, x_3, 2 * x_3]
  let x2 := toBitVecValue 64 #v[x_4, 2 * x_4, x_1, 2 * x_1, 2 * x_1, 2 * x_1, 2 * x_1, 0]
  let x4 := toBitVecValue 64 #v[2 * x_3, 0, x_5, 0, x_2, 2 * x_2, 2 * x_2, 2 * x_2]

  have v82Value : v82 = x0 := by denote_vecbin hv82
  have v83Value : v83 = x2 := by denote_vecbin hv83
  have v84Value : v84 = x4 := by denote_vecbin hv84

  subst v82Value v83Value v84Value
  denote_clear v 76 84

  denote_step_all v 97

  -- `%85`-`%87` = `p0l`, `p1l`, `p2l`: `wwl_madd52lo( zero, x_, x_ )`.
  let p0l := toBitVecValue 64 #v[pl (x_0) (x_0), pl (2 * x_0) (x_1), pl (2 * x_0) (x_2), pl (2 * x_0) (x_3), pl (2 * x_0) (x_4), pl (2 * x_0) (x_5), pl (x_3) (x_3), pl (2 * x_3) (x_4)]
  let p1l := toBitVecValue 64 #v[pl (x_4) (x_4), pl (2 * x_4) (x_5), pl (x_1) (x_1), pl (2 * x_1) (x_2), pl (2 * x_1) (x_3), pl (2 * x_1) (x_4), pl (2 * x_1) (x_5), 0]
  let p2l := toBitVecValue 64 #v[pl (2 * x_3) (x_5), 0, pl (x_5) (x_5), 0, pl (x_2) (x_2), pl (2 * x_2) (x_3), pl (2 * x_2) (x_4), pl (2 * x_2) (x_5)]
  have v85Value : v85 = p0l := by sqr_vpmadd52 hv85
  have v86Value : v86 = p1l := by sqr_vpmadd52 hv86
  have v87Value : v87 = p2l := by sqr_vpmadd52 hv87

  -- `%89`, `%91`, `%93` = `p0h`, `p1h`, `p2h`: `wwl_shl( wwl_madd52hi( zero, .. ), 9 )`.
  -- The unshifted `%88`/`%90`/`%92` are unnamed in the source.
  let p0hRaw := toBitVecValue 64 #v[phRaw (x_0) (x_0), phRaw (2 * x_0) (x_1), phRaw (2 * x_0) (x_2), phRaw (2 * x_0) (x_3), phRaw (2 * x_0) (x_4), phRaw (2 * x_0) (x_5), phRaw (x_3) (x_3), phRaw (2 * x_3) (x_4)]
  let p1hRaw := toBitVecValue 64 #v[phRaw (x_4) (x_4), phRaw (2 * x_4) (x_5), phRaw (x_1) (x_1), phRaw (2 * x_1) (x_2), phRaw (2 * x_1) (x_3), phRaw (2 * x_1) (x_4), phRaw (2 * x_1) (x_5), 0]
  let p2hRaw := toBitVecValue 64 #v[phRaw (2 * x_3) (x_5), 0, phRaw (x_5) (x_5), 0, phRaw (x_2) (x_2), phRaw (2 * x_2) (x_3), phRaw (2 * x_2) (x_4), phRaw (2 * x_2) (x_5)]
  have v88Value : v88 = p0hRaw := by sqr_vpmadd52 hv88
  have v90Value : v90 = p1hRaw := by sqr_vpmadd52 hv90
  have v92Value : v92 = p2hRaw := by sqr_vpmadd52 hv92
  subst v88Value v90Value v92Value

  let p0h := toBitVecValue 64 #v[ph (x_0) (x_0), ph (2 * x_0) (x_1), ph (2 * x_0) (x_2), ph (2 * x_0) (x_3), ph (2 * x_0) (x_4), ph (2 * x_0) (x_5), ph (x_3) (x_3), ph (2 * x_3) (x_4)]
  let p1h := toBitVecValue 64 #v[ph (x_4) (x_4), ph (2 * x_4) (x_5), ph (x_1) (x_1), ph (2 * x_1) (x_2), ph (2 * x_1) (x_3), ph (2 * x_1) (x_4), ph (2 * x_1) (x_5), 0]
  let p2h := toBitVecValue 64 #v[ph (2 * x_3) (x_5), 0, ph (x_5) (x_5), 0, ph (x_2) (x_2), ph (2 * x_2) (x_3), ph (2 * x_2) (x_4), ph (2 * x_2) (x_5)]
  have v89Value : v89 = p0h := by denote_vecbin hv89
  have v91Value : v91 = p1h := by denote_vecbin hv91
  have v93Value : v93 = p2h := by denote_vecbin hv93

  -- `%94`-`%97`: the `wwl_andnot( mask1/mask2, p.. )` terms -- the lanes
  -- belonging to the *low* word. Unnamed in the source, where they appear
  -- inline in `zll` and `zlh`.
  subst v86Value v87Value v91Value v93Value
  let p1lLow := toBitVecValue 64 #v[0, 0, pl (x_1) (x_1), pl (2 * x_1) (x_2), pl (2 * x_1) (x_3), pl (2 * x_1) (x_4), pl (2 * x_1) (x_5), 0]
  let p2lLow := toBitVecValue 64 #v[0, 0, 0, 0, pl (x_2) (x_2), pl (2 * x_2) (x_3), pl (2 * x_2) (x_4), pl (2 * x_2) (x_5)]
  let p1hLow := toBitVecValue 64 #v[0, 0, ph (x_1) (x_1), ph (2 * x_1) (x_2), ph (2 * x_1) (x_3), ph (2 * x_1) (x_4), ph (2 * x_1) (x_5), 0]
  let p2hLow := toBitVecValue 64 #v[0, 0, 0, 0, ph (x_2) (x_2), ph (2 * x_2) (x_3), ph (2 * x_2) (x_4), ph (2 * x_2) (x_5)]
  have v94Value : v94 = p1lLow := by denote_vecbin hv94
  have v95Value : v95 = p2lLow := by denote_vecbin hv95
  have v96Value : v96 = p1hLow := by denote_vecbin hv96
  have v97Value : v97 = p2hLow := by denote_vecbin hv97

  subst v85Value v89Value v94Value v95Value v96Value v97Value
  denote_clear v 85 97

  denote_step_all v 107

  -- `%98`/`%106` are unnamed in the source: LLVM reassociated
  -- `wwl_add( p0_, wwl_add( a, b ) )` into `(a + p0_) + b`.
  -- `%99` = `zlh`, `%107` = `zll`.
  let zlhPart := toBitVecValue 64 #v[0 + ph (x_0) (x_0), 0 + ph (2 * x_0) (x_1), ph (x_1) (x_1) + ph (2 * x_0) (x_2), ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3), ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4), ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5), ph (2 * x_1) (x_5) + ph (x_3) (x_3), 0 + ph (2 * x_3) (x_4)]
  let zlh := toBitVecValue 64 #v[(0 + ph (x_0) (x_0)) + 0, (0 + ph (2 * x_0) (x_1)) + 0, (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4), (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)]
  have v98Value : v98 = zlhPart := by denote_vecbin hv98
  subst v98Value
  have v99Value : v99 = zlh := by denote_vecbin hv99

  let zllPart := toBitVecValue 64 #v[0 + pl (x_0) (x_0), 0 + pl (2 * x_0) (x_1), pl (x_1) (x_1) + pl (2 * x_0) (x_2), pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3), pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4), pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5), pl (2 * x_1) (x_5) + pl (x_3) (x_3), 0 + pl (2 * x_3) (x_4)]
  let zll := toBitVecValue 64 #v[(0 + pl (x_0) (x_0)) + 0, (0 + pl (2 * x_0) (x_1)) + 0, (pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0, (pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0, (pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2), (pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3), (pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4), (0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5)]
  have v106Value : v106 = zllPart := by denote_vecbin hv106
  subst v106Value
  have v107Value : v107 = zll := by denote_vecbin hv107

  denote_step_all v 111

  -- `%100`-`%103`: the `wwl_and( mask1/mask2, p.. )` terms -- the lanes belonging
  -- to the *high* word. The masks are the poisoned `%30`/`%39`/`%48`/`%57`, so
  -- these carry poison lanes and are not of the `.map PoisonOr.value` shape.
  let p1lHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (x_4) (x_4))), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  let p2lHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (pl (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  let p1hHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (ph (x_4) (x_4))), .value (BitVec.ofNat 64 (ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison, .poison]
  let p2hHigh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (ph (2 * x_3) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison, .poison]
  have v100Value : v100 = p1lHigh := by denote_vecbin hv100
  have v101Value : v101 = p2lHigh := by denote_vecbin hv101
  have v102Value : v102 = p1hHigh := by denote_vecbin hv102
  have v103Value : v103 = p2hHigh := by denote_vecbin hv103
  subst v100Value v101Value v102Value v103Value

  -- `%104` = `zhh`, `%111` = `zhl`.
  let zhh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (ph (2 * x_3) (x_5) + ph (x_4) (x_4))), .value (BitVec.ofNat 64 (ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison, .poison]
  let zhl : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5) + pl (x_4) (x_4))), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (pl (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v104Value : v104 = zhh := by denote_vecbin hv104
  have v111Value : v111 = zhl := by denote_vecbin hv111

  subst v99Value v107Value v104Value v111Value
  denote_step_all v 115

  -- `%105`, `%109`, `%110` are `wwl_slide`: `shufflevector` whose mask reaches
  -- into the *second* operand.
  let zlhSlide := toBitVecValue 64 #v[0, (0 + ph (x_0) (x_0)) + 0, (0 + ph (2 * x_0) (x_1)) + 0, (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)]
  have v105Value : v105 = zlhSlide := by sqr_shuffle hv105
  subst v105Value

  -- `%108` = `zl`.
  let zl := toBitVecValue 64 #v[(0 + pl (x_0) (x_0)) + 0 + 0, (0 + pl (2 * x_0) (x_1)) + 0 + (0 + ph (x_0) (x_0)) + 0, (pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0 + (0 + ph (2 * x_0) (x_1)) + 0, (pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0 + (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2) + (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3) + (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), (pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)]
  have v108Value : v108 = zl := by denote_vecbin hv108
  subst v108Value

  let zhhSlide : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (ph (2 * x_3) (x_5) + ph (x_4) (x_4))), .value (BitVec.ofNat 64 (ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  let zlhSlide7 : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 ((0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v109Value : v109 = zhhSlide := by sqr_shuffle hv109
  have v110Value : v110 = zlhSlide7 := by sqr_shuffle hv110
  subst v109Value v110Value

  -- `%113` = `zh`.
  let zhPart : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0)), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4))), .value (BitVec.ofNat 64 (pl (x_5) (x_5) + ph (2 * x_4) (x_5))), .value (BitVec.ofNat 64 (0 + ph (x_5) (x_5))), .value (BitVec.ofNat 64 (0 + 0)), .value (BitVec.ofNat 64 (0 + 0)), .poison, .poison]
  let zh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5))), .value (BitVec.ofNat 64 (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0)), .value (BitVec.ofNat 64 (pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0)), .value (BitVec.ofNat 64 (0 + ph (x_5) (x_5) + 0)), .value (BitVec.ofNat 64 (0 + 0 + 0)), .value (BitVec.ofNat 64 (0 + 0 + 0)), .poison, .poison]
  have v112Value : v112 = zhPart := by denote_vecbin hv112
  subst v112Value
  have v113Value : v113 = zh := by denote_vecbin hv113
  subst v113Value

  -- `%114` = `za`, `%115` = `zb`.
  let za := toBitVecValue 64 #v[(0 + pl (x_0) (x_0)) + 0 + 0, (0 + pl (2 * x_0) (x_1)) + 0 + (0 + ph (x_0) (x_0)) + 0, (pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0 + (0 + ph (2 * x_0) (x_1)) + 0, (pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0 + (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0, (pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2) + (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0, (pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3) + (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2), 0, 0]
  let zb := toBitVecValue 64 #v[(pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3), (0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4), pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5), pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0, pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0, 0 + ph (x_5) (x_5) + 0, 0 + 0 + 0, 0 + 0 + 0]
  have v114Value : v114 = za := by denote_vecbin hv114
  have v115Value : v115 = zb := by sqr_shuffle hv115

  subst v114Value v115Value
  denote_step_all v 119

  -- `%116`-`%119`: the final fold.
  let zbShl7 := toBitVecValue 64 #v[((pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3)) * 128, ((0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)) * 128, (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)) * 128, (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0) * 128, (pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0) * 128, (0 + ph (x_5) (x_5) + 0) * 128, (0 + 0 + 0) * 128, (0 + 0 + 0) * 128]
  have v76Value : v116 = zbShl7 := by denote_vecbin hv116
  subst v76Value
  let zbShl7Za := toBitVecValue 64 #v[(((pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3)) * 128) + ((0 + pl (x_0) (x_0)) + 0 + 0), (((0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)) * 128) + ((0 + pl (2 * x_0) (x_1)) + 0 + (0 + ph (x_0) (x_0)) + 0), ((pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)) * 128) + ((pl (x_1) (x_1) + pl (2 * x_0) (x_2)) + 0 + (0 + ph (2 * x_0) (x_1)) + 0), ((pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0) * 128) + ((pl (2 * x_1) (x_2) + pl (2 * x_0) (x_3)) + 0 + (ph (x_1) (x_1) + ph (2 * x_0) (x_2)) + 0), ((pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0) * 128) + ((pl (2 * x_1) (x_3) + pl (2 * x_0) (x_4)) + pl (x_2) (x_2) + (ph (2 * x_1) (x_2) + ph (2 * x_0) (x_3)) + 0), ((0 + ph (x_5) (x_5) + 0) * 128) + ((pl (2 * x_1) (x_4) + pl (2 * x_0) (x_5)) + pl (2 * x_2) (x_3) + (ph (2 * x_1) (x_3) + ph (2 * x_0) (x_4)) + ph (x_2) (x_2)), ((0 + 0 + 0) * 128) + (0), ((0 + 0 + 0) * 128) + (0)]
  let zbMul24 := toBitVecValue 64 #v[((pl (2 * x_1) (x_5) + pl (x_3) (x_3)) + pl (2 * x_2) (x_4) + (ph (2 * x_1) (x_4) + ph (2 * x_0) (x_5)) + ph (2 * x_2) (x_3)) * 24, ((0 + pl (2 * x_3) (x_4)) + pl (2 * x_2) (x_5) + (ph (2 * x_1) (x_5) + ph (x_3) (x_3)) + ph (2 * x_2) (x_4)) * 24, (pl (2 * x_3) (x_5) + pl (x_4) (x_4) + 0 + (0 + ph (2 * x_3) (x_4)) + ph (2 * x_2) (x_5)) * 24, (pl (2 * x_4) (x_5) + ph (2 * x_3) (x_5) + ph (x_4) (x_4) + 0) * 24, (pl (x_5) (x_5) + ph (2 * x_4) (x_5) + 0) * 24, (0 + ph (x_5) (x_5) + 0) * 24, (0 + 0 + 0) * 24, (0 + 0 + 0) * 24]
  have v77Value : v117 = zbShl7Za := by denote_vecbin hv117
  have v78Value : v118 = zbMul24 := by denote_vecbin hv118
  subst v77Value v78Value
  -- `%119`: the final add, against `sqrVec` directly; the lane sums are
  -- already ℕ-level, so only `sqLimb` unfolding and `ring` remain.
  have v79Value : v119 = (sqrVec x).map PoisonOr.value := by
    simp only [sqrVec, limbVec]
    denote_vecbin hv119
    all_goals try congr 1
    all_goals try simp [sqLimb, sqCol, limbNat, ph, pl]
    all_goals try ring_nf
  subst v79Value
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
  have b0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0
  have b1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1
  have b2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2
  have b3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3
  have b4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4
  have b5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5
  have hbnd : ∀ (i: Fin 6), limbNat x i < 2^47 := limbNat_lt x 47 (by omega) hx
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
      = ((decodeNat (limbNat x) : ℕ) : Int) from by simp [decodeNat_eq]; try ring]
  -- 3. both sides are now casts of `decodeNat`, so `decodeLimbs_sqLimb_zmod` applies
  push_cast
  exact decodeLimbs_sqLimb_zmod (limbNat x)

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
    (hb : ∀ k, sqLimb (limbNat x) k < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (sqrValue x).getValue
      ∧ R43x6.BoundedLower 0 (sqrValue x).getValue := by
  have hv : (sqrValue x).getValue = sqrVec x := by rw [sqrValue_eq x hx h7]; rfl
  rw [hv, sqrVec]
  exact limbVec_bounds _ N (by omega) hb

private theorem output_u44 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u44_u61 x := by
  intro hin
  have hb : ∀ k, sqLimb (limbNat x) k < 2^61 := fun k =>
    sqLimb_lt_u44 _ (limbNat_lt x 44 (by omega) hin) k
  exact_mod_cast output_bounds_of x (2^61) (by omega) hx h7 hb

private theorem output_u45 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u45_u61 x := by
  intro hin
  have hb : ∀ k, sqLimb (limbNat x) k < 2^61 := fun k =>
    sqLimb_lt_u45 _ (limbNat_lt x 45 (by omega) hin) k
  exact_mod_cast output_bounds_of x (2^61) (by omega) hx h7 hb

private theorem output_u46 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u46_u62 x := by
  intro hin
  have hb : ∀ k, sqLimb (limbNat x) k < 2^62 := fun k =>
    sqLimb_lt_u46 _ (limbNat_lt x 46 (by omega) hin) k
  exact_mod_cast output_bounds_of x (2^62) (by omega) hx h7 hb

private theorem output_u47 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u47_u62 x := by
  intro hin
  have hb : ∀ k, sqLimb (limbNat x) k < 2^62 := fun k =>
    sqLimb_lt_u47 _ (limbNat_lt x 47 (by omega) hin) k
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

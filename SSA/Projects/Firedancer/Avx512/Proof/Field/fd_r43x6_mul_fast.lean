/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: the bulk of this file was machine-generated; the structure mirrors
the data flow of `fd_r43x6_mul_fast`.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_mul_fast
public import SSA.Projects.Firedancer.Avx512.Proof.Common
public import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_mul_fast
public import SSA.Projects.Firedancer.MLIR.Poison
public import SSA.Projects.Firedancer.Ed25519

/-!
# `fd_r43x6_mul_fast` multiplies in `ZMod p`

Denoting the lifted SLLVM program and decoding the six output limbs yields the
product of the decoded inputs in `GF(2^255 - 19)`, within the widths the
`fd_r43x6.h` table promises.

The derivation runs at the N level throughout: each of the 146 instructions is
reduced to a vector of `BitVec.ofNat 64` applied to an expression over `pl`
and `ph` (`Spec/Common.lean`), so `denote_fd_r43x6_mul_fast` lands directly on
the specified `mulVec x y` and the ring correctness of `Spec/` applies without
an intermediate lane expression to transfer.

Intermediates carry the variable names from `fd_r43x6.h` (`x0`-`x5` broadcasts
as `xb0`-`xb5`, `t0`-`t6`, `p1j`-`p6j`/`q3j`-`q6j`, `zl`/`zh`, `za`/`zb`).

Note that in the valuation, `%arg0` (= `x`) is the *second* component of
`Ctxt.Valuation.ofPair` and `%arg1` (= `y`) the first: `ofPair` builds the
context `[t1, t2]` with `%arg1` as variable 0.

## Hypotheses

`R43x6.Unreduced x`, `R43x6.Unreduced y` and `y[6] = y[7] = 0`, the contract
stated in `fd_r43x6.h`. The lane bounds are what make each `vpmadd52`
truncation the identity; the two zero lanes of `y` are consumed at the
`vpmadd52` instructions that read `y`, so no product against them is ever
formed. Lanes 6 and 7 of `x` are ignored by the program itself (the
`wwl_permute` masks select only lanes 0-5) and so are unconstrained.
-/

@[expose] public section

namespace Firedancer.Avx512

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! The bound facts the per-opcode tactics need, bound once here rather than at
each of the instructions that needs them. `Lean.mkIdent` escapes macro hygiene
so these refer to the `have`s of the theorem below, which the generated body
names by convention. -/

local macro "mul_shuffle " h:term : tactic =>
  `(tactic| denote_shuffle $h with $(Lean.mkIdent `hy6):ident, $(Lean.mkIdent `hy7):ident)

local macro "mul_vpmadd52 " h:term : tactic =>
  `(tactic|
    denote_vpmadd52 $h with $(Lean.mkIdent `hy6):ident, $(Lean.mkIdent `hy7):ident,
      Nat.mod_eq_of_lt $(Lean.mkIdent `tx0), Nat.mod_eq_of_lt $(Lean.mkIdent `tx1),
      Nat.mod_eq_of_lt $(Lean.mkIdent `tx2), Nat.mod_eq_of_lt $(Lean.mkIdent `tx3),
      Nat.mod_eq_of_lt $(Lean.mkIdent `tx4), Nat.mod_eq_of_lt $(Lean.mkIdent `tx5),
      Nat.mod_eq_of_lt $(Lean.mkIdent `ty0), Nat.mod_eq_of_lt $(Lean.mkIdent `ty1),
      Nat.mod_eq_of_lt $(Lean.mkIdent `ty2), Nat.mod_eq_of_lt $(Lean.mkIdent `ty3),
      Nat.mod_eq_of_lt $(Lean.mkIdent `ty4), Nat.mod_eq_of_lt $(Lean.mkIdent `ty5))

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- **Limb derivation** for `fd_r43x6_mul_fast`: on unreduced inputs whose
two high `y` lanes are zero, the denotation *is* the specified limb vector
`mulVec x y` -- every one of the 146 instructions carried through at the N
level. -/
theorem denote_fd_r43x6_mul_fast (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    fd_r43x6_mul_fast.denote (Ctxt.Valuation.ofPair (y.map PoisonOr.value) (x.map PoisonOr.value)) =
      ([(mulVec x y).map PoisonOr.value]ₕ :
        HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))]) := by
  -- The operand bounds that make each `vpmadd52` truncation the identity.
  have bx0 : x[0].toNat < 2 ^ 47 := unn_toNat x 47 (by omega) hx 0
  have bx1 : x[1].toNat < 2 ^ 47 := unn_toNat x 47 (by omega) hx 1
  have bx2 : x[2].toNat < 2 ^ 47 := unn_toNat x 47 (by omega) hx 2
  have bx3 : x[3].toNat < 2 ^ 47 := unn_toNat x 47 (by omega) hx 3
  have bx4 : x[4].toNat < 2 ^ 47 := unn_toNat x 47 (by omega) hx 4
  have bx5 : x[5].toNat < 2 ^ 47 := unn_toNat x 47 (by omega) hx 5
  have by0 : y[0].toNat < 2 ^ 47 := unn_toNat y 47 (by omega) hy 0
  have by1 : y[1].toNat < 2 ^ 47 := unn_toNat y 47 (by omega) hy 1
  have by2 : y[2].toNat < 2 ^ 47 := unn_toNat y 47 (by omega) hy 2
  have by3 : y[3].toNat < 2 ^ 47 := unn_toNat y 47 (by omega) hy 3
  have by4 : y[4].toNat < 2 ^ 47 := unn_toNat y 47 (by omega) hy 4
  have by5 : y[5].toNat < 2 ^ 47 := unn_toNat y 47 (by omega) hy 5
  have tx0 : x[0].toNat < 4503599627370496 := by omega
  have tx1 : x[1].toNat < 4503599627370496 := by omega
  have tx2 : x[2].toNat < 4503599627370496 := by omega
  have tx3 : x[3].toNat < 4503599627370496 := by omega
  have tx4 : x[4].toNat < 4503599627370496 := by omega
  have tx5 : x[5].toNat < 4503599627370496 := by omega
  have ty0 : y[0].toNat < 4503599627370496 := by omega
  have ty1 : y[1].toNat < 4503599627370496 := by omega
  have ty2 : y[2].toNat < 4503599627370496 := by omega
  have ty3 : y[3].toNat < 4503599627370496 := by omega
  have ty4 : y[4].toNat < 4503599627370496 := by omega
  have ty5 : y[5].toNat < 4503599627370496 := by omega
  unfold fd_r43x6_mul_fast
  denote_step_reduce v 96 [LLVM.const?, LLVM.Ty.poison] fold
  let zeroBVP : PoisonOr (BitVec 64) := .value 0
  let neg1BVP : PoisonOr (BitVec 64) := .value (-1)
  -- `%0`-`%2`, `%11`, `%12`: the dense constants.
  let zaMask : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, zeroBVP, zeroBVP]
  let dense7 := toBitVecValue 64 (Vector.replicate 8 7)
  let dense24 := toBitVecValue 64 (Vector.replicate 8 24)
  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)
  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)
  have v0Value : v0 = dense24 := by denote_dense hv0
  have v1Value : v1 = dense7 := by denote_dense hv1
  have v2Value : v2 = zaMask := by denote_dense hv2
  have v11Value : v11 = nineVec := by denote_dense hv11
  have v12Value : v12 = zeroVec := by denote_dense hv12
  -- `%24`, `%33`, …, `%96`: the `wwl_slide` zero operands, zero in the lanes each slide reads.
  let p7z1 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 7 (PoisonOr.poison : PoisonOr (BitVec 64))).append
      (Vector.replicate 1 (.value (BitVec.zero 64)))
  let p6z2 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 6 (PoisonOr.poison : PoisonOr (BitVec 64))).append
      (Vector.replicate 2 (.value (BitVec.zero 64)))
  let p5z3 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 5 (PoisonOr.poison : PoisonOr (BitVec 64))).append
      (Vector.replicate 3 (.value (BitVec.zero 64)))
  let z3p5 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 3 (PoisonOr.value (BitVec.zero 64))).append
      (Vector.replicate 5 (.poison : PoisonOr (BitVec 64)))
  let p4z4 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 4 (PoisonOr.poison : PoisonOr (BitVec 64))).append
      (Vector.replicate 4 (.value (BitVec.zero 64)))
  let z2p6 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 2 (PoisonOr.value (BitVec.zero 64))).append
      (Vector.replicate 6 (.poison : PoisonOr (BitVec 64)))
  let p3z5 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 3 (PoisonOr.poison : PoisonOr (BitVec 64))).append
      (Vector.replicate 5 (.value (BitVec.zero 64)))
  let z1p7 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 1 (PoisonOr.value (BitVec.zero 64))).append
      (Vector.replicate 7 (.poison : PoisonOr (BitVec 64)))
  let p2z6 : Vector (PoisonOr (BitVec 64)) 8 :=
    (Vector.replicate 2 (PoisonOr.poison : PoisonOr (BitVec 64))).append
      (Vector.replicate 6 (.value (BitVec.zero 64)))
  have v24Value : v24 = p7z1 := by
    simp only [hv24]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, p7z1] <;> rfl
  have v33Value : v33 = p6z2 := by
    simp only [hv33]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, p6z2] <;> rfl
  have v42Value : v42 = p5z3 := by
    simp only [hv42]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, p5z3] <;> rfl
  have v51Value : v51 = z3p5 := by
    simp only [hv51]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, z3p5] <;> rfl
  have v60Value : v60 = p4z4 := by
    simp only [hv60]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, p4z4] <;> rfl
  have v69Value : v69 = z2p6 := by
    simp only [hv69]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, z2p6] <;> rfl
  have v78Value : v78 = p3z5 := by
    simp only [hv78]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, p3z5] <;> rfl
  have v87Value : v87 = z1p7 := by
    simp only [hv87]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, z1p7] <;> rfl
  have v96Value : v96 = p2z6 := by
    simp only [hv96]; apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, p2z6] <;> rfl
  subst v0Value v1Value v2Value v11Value v12Value
  subst v24Value v33Value v42Value v51Value v60Value v69Value v78Value v87Value v96Value
  denote_clear v 0 96
  -- Name the lanes once, so the uses below do not each re-elaborate an
  -- `x[i]`/`y[j]` bounds proof.
  let x_0 : ℕ := limbNat x 0
  let x_1 : ℕ := limbNat x 1
  let x_2 : ℕ := limbNat x 2
  let x_3 : ℕ := limbNat x 3
  let x_4 : ℕ := limbNat x 4
  let x_5 : ℕ := limbNat x 5
  let y_0 : ℕ := limbNat y 0
  let y_1 : ℕ := limbNat y 1
  let y_2 : ℕ := limbNat y 2
  let y_3 : ℕ := limbNat y 3
  let y_4 : ℕ := limbNat y 4
  let y_5 : ℕ := limbNat y 5
  -- `%97`-`%102` = `x0`-`x5`: `wwl_permute( wwl_bcast( iL ), x )`.
  denote_step_all v 102
  let xb0 := toBitVecValue 64 #v[x_0, x_0, x_0, x_0, x_0, x_0, x_0, x_0]
  let xb1 := toBitVecValue 64 #v[x_1, x_1, x_1, x_1, x_1, x_1, x_1, x_1]
  let xb2 := toBitVecValue 64 #v[x_2, x_2, x_2, x_2, x_2, x_2, x_2, x_2]
  let xb3 := toBitVecValue 64 #v[x_3, x_3, x_3, x_3, x_3, x_3, x_3, x_3]
  let xb4 := toBitVecValue 64 #v[x_4, x_4, x_4, x_4, x_4, x_4, x_4, x_4]
  let xb5 := toBitVecValue 64 #v[x_5, x_5, x_5, x_5, x_5, x_5, x_5, x_5]
  have v97Value : v97 = xb0 := by mul_shuffle hv97
  have v98Value : v98 = xb1 := by mul_shuffle hv98
  have v99Value : v99 = xb2 := by mul_shuffle hv99
  have v100Value : v100 = xb3 := by mul_shuffle hv100
  have v101Value : v101 = xb4 := by mul_shuffle hv101
  have v102Value : v102 = xb5 := by mul_shuffle hv102
  subst v97Value v98Value v99Value v100Value v101Value v102Value
  denote_clear v 97 102
  -- `%103`-`%120` = `t0`-`t6`: `t_i = wwl_madd52lo( wwl_shl( wwl_madd52hi( zero, x_(i-1), y ), 9 ), x_i, y )`.
  denote_step_all v 120
  let t0 :=
    toBitVecValue 64
      #v[pl (x_0) (y_0), pl (x_0) (y_1), pl (x_0) (y_2), pl (x_0) (y_3), pl (x_0) (y_4),
        pl (x_0) (y_5), 0, 0]
  have v103Value : v103 = t0 := by mul_vpmadd52 hv103
  subst v103Value
  let hi0 :=
    toBitVecValue 64
      #v[phRaw (x_0) (y_0), phRaw (x_0) (y_1), phRaw (x_0) (y_2), phRaw (x_0) (y_3),
        phRaw (x_0) (y_4), phRaw (x_0) (y_5), 0, 0]
  have v104Value : v104 = hi0 := by mul_vpmadd52 hv104
  subst v104Value
  let hs0 :=
    toBitVecValue 64
      #v[ph (x_0) (y_0), ph (x_0) (y_1), ph (x_0) (y_2), ph (x_0) (y_3), ph (x_0) (y_4),
        ph (x_0) (y_5), 0, 0]
  have v105Value : v105 = hs0 := by denote_vecbin hv105
  subst v105Value
  let t1 :=
    toBitVecValue 64
      #v[ph (x_0) (y_0) + pl (x_1) (y_0), ph (x_0) (y_1) + pl (x_1) (y_1),
        ph (x_0) (y_2) + pl (x_1) (y_2), ph (x_0) (y_3) + pl (x_1) (y_3),
        ph (x_0) (y_4) + pl (x_1) (y_4), ph (x_0) (y_5) + pl (x_1) (y_5), 0, 0]
  have v106Value : v106 = t1 := by mul_vpmadd52 hv106
  subst v106Value
  let hi1 :=
    toBitVecValue 64
      #v[phRaw (x_1) (y_0), phRaw (x_1) (y_1), phRaw (x_1) (y_2), phRaw (x_1) (y_3),
        phRaw (x_1) (y_4), phRaw (x_1) (y_5), 0, 0]
  have v107Value : v107 = hi1 := by mul_vpmadd52 hv107
  subst v107Value
  let hs1 :=
    toBitVecValue 64
      #v[ph (x_1) (y_0), ph (x_1) (y_1), ph (x_1) (y_2), ph (x_1) (y_3), ph (x_1) (y_4),
        ph (x_1) (y_5), 0, 0]
  have v108Value : v108 = hs1 := by denote_vecbin hv108
  subst v108Value
  let t2 :=
    toBitVecValue 64
      #v[ph (x_1) (y_0) + pl (x_2) (y_0), ph (x_1) (y_1) + pl (x_2) (y_1),
        ph (x_1) (y_2) + pl (x_2) (y_2), ph (x_1) (y_3) + pl (x_2) (y_3),
        ph (x_1) (y_4) + pl (x_2) (y_4), ph (x_1) (y_5) + pl (x_2) (y_5), 0, 0]
  have v109Value : v109 = t2 := by mul_vpmadd52 hv109
  subst v109Value
  let hi2 :=
    toBitVecValue 64
      #v[phRaw (x_2) (y_0), phRaw (x_2) (y_1), phRaw (x_2) (y_2), phRaw (x_2) (y_3),
        phRaw (x_2) (y_4), phRaw (x_2) (y_5), 0, 0]
  have v110Value : v110 = hi2 := by mul_vpmadd52 hv110
  subst v110Value
  let hs2 :=
    toBitVecValue 64
      #v[ph (x_2) (y_0), ph (x_2) (y_1), ph (x_2) (y_2), ph (x_2) (y_3), ph (x_2) (y_4),
        ph (x_2) (y_5), 0, 0]
  have v111Value : v111 = hs2 := by denote_vecbin hv111
  subst v111Value
  let t3 :=
    toBitVecValue 64
      #v[ph (x_2) (y_0) + pl (x_3) (y_0), ph (x_2) (y_1) + pl (x_3) (y_1),
        ph (x_2) (y_2) + pl (x_3) (y_2), ph (x_2) (y_3) + pl (x_3) (y_3),
        ph (x_2) (y_4) + pl (x_3) (y_4), ph (x_2) (y_5) + pl (x_3) (y_5), 0, 0]
  have v112Value : v112 = t3 := by mul_vpmadd52 hv112
  subst v112Value
  let hi3 :=
    toBitVecValue 64
      #v[phRaw (x_3) (y_0), phRaw (x_3) (y_1), phRaw (x_3) (y_2), phRaw (x_3) (y_3),
        phRaw (x_3) (y_4), phRaw (x_3) (y_5), 0, 0]
  have v113Value : v113 = hi3 := by mul_vpmadd52 hv113
  subst v113Value
  let hs3 :=
    toBitVecValue 64
      #v[ph (x_3) (y_0), ph (x_3) (y_1), ph (x_3) (y_2), ph (x_3) (y_3), ph (x_3) (y_4),
        ph (x_3) (y_5), 0, 0]
  have v114Value : v114 = hs3 := by denote_vecbin hv114
  subst v114Value
  let t4 :=
    toBitVecValue 64
      #v[ph (x_3) (y_0) + pl (x_4) (y_0), ph (x_3) (y_1) + pl (x_4) (y_1),
        ph (x_3) (y_2) + pl (x_4) (y_2), ph (x_3) (y_3) + pl (x_4) (y_3),
        ph (x_3) (y_4) + pl (x_4) (y_4), ph (x_3) (y_5) + pl (x_4) (y_5), 0, 0]
  have v115Value : v115 = t4 := by mul_vpmadd52 hv115
  subst v115Value
  let hi4 :=
    toBitVecValue 64
      #v[phRaw (x_4) (y_0), phRaw (x_4) (y_1), phRaw (x_4) (y_2), phRaw (x_4) (y_3),
        phRaw (x_4) (y_4), phRaw (x_4) (y_5), 0, 0]
  have v116Value : v116 = hi4 := by mul_vpmadd52 hv116
  subst v116Value
  let hs4 :=
    toBitVecValue 64
      #v[ph (x_4) (y_0), ph (x_4) (y_1), ph (x_4) (y_2), ph (x_4) (y_3), ph (x_4) (y_4),
        ph (x_4) (y_5), 0, 0]
  have v117Value : v117 = hs4 := by denote_vecbin hv117
  subst v117Value
  let t5 :=
    toBitVecValue 64
      #v[ph (x_4) (y_0) + pl (x_5) (y_0), ph (x_4) (y_1) + pl (x_5) (y_1),
        ph (x_4) (y_2) + pl (x_5) (y_2), ph (x_4) (y_3) + pl (x_5) (y_3),
        ph (x_4) (y_4) + pl (x_5) (y_4), ph (x_4) (y_5) + pl (x_5) (y_5), 0, 0]
  have v118Value : v118 = t5 := by mul_vpmadd52 hv118
  subst v118Value
  let hi5 :=
    toBitVecValue 64
      #v[phRaw (x_5) (y_0), phRaw (x_5) (y_1), phRaw (x_5) (y_2), phRaw (x_5) (y_3),
        phRaw (x_5) (y_4), phRaw (x_5) (y_5), 0, 0]
  have v119Value : v119 = hi5 := by mul_vpmadd52 hv119
  subst v119Value
  let t6 :=
    toBitVecValue 64
      #v[ph (x_5) (y_0), ph (x_5) (y_1), ph (x_5) (y_2), ph (x_5) (y_3), ph (x_5) (y_4),
        ph (x_5) (y_5), 0, 0]
  have v120Value : v120 = t6 := by denote_vecbin hv120
  subst v120Value
  denote_clear v 103 120
  -- `%121`-`%130`: the `wwl_slide` shuffles `p1j`-`p6j` and `q3j`-`q6j`.
  denote_step_all v 130
  let p1j :=
    toBitVecValue 64
      #v[0, (ph (x_0) (y_0) + pl (x_1) (y_0)), (ph (x_0) (y_1) + pl (x_1) (y_1)),
        (ph (x_0) (y_2) + pl (x_1) (y_2)), (ph (x_0) (y_3) + pl (x_1) (y_3)),
        (ph (x_0) (y_4) + pl (x_1) (y_4)), (ph (x_0) (y_5) + pl (x_1) (y_5)), 0]
  have v121Value : v121 = p1j := by mul_shuffle hv121
  subst v121Value
  let p2j :=
    toBitVecValue 64
      #v[0, 0, (ph (x_1) (y_0) + pl (x_2) (y_0)), (ph (x_1) (y_1) + pl (x_2) (y_1)),
        (ph (x_1) (y_2) + pl (x_2) (y_2)), (ph (x_1) (y_3) + pl (x_2) (y_3)),
        (ph (x_1) (y_4) + pl (x_2) (y_4)), (ph (x_1) (y_5) + pl (x_2) (y_5))]
  have v122Value : v122 = p2j := by mul_shuffle hv122
  subst v122Value
  let p3j :=
    toBitVecValue 64
      #v[0, 0, 0, (ph (x_2) (y_0) + pl (x_3) (y_0)), (ph (x_2) (y_1) + pl (x_3) (y_1)),
        (ph (x_2) (y_2) + pl (x_3) (y_2)), (ph (x_2) (y_3) + pl (x_3) (y_3)),
        (ph (x_2) (y_4) + pl (x_3) (y_4))]
  have v123Value : v123 = p3j := by mul_shuffle hv123
  subst v123Value
  let q3j : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[.value (BitVec.ofNat 64 ((ph (x_2) (y_5) + pl (x_3) (y_5)))), .value (BitVec.ofNat 64 (0)),
      .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)),
      .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v124Value : v124 = q3j := by mul_shuffle hv124
  subst v124Value
  let p4j :=
    toBitVecValue 64
      #v[0, 0, 0, 0, (ph (x_3) (y_0) + pl (x_4) (y_0)), (ph (x_3) (y_1) + pl (x_4) (y_1)),
        (ph (x_3) (y_2) + pl (x_4) (y_2)), (ph (x_3) (y_3) + pl (x_4) (y_3))]
  have v125Value : v125 = p4j := by mul_shuffle hv125
  subst v125Value
  let q4j : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[.value (BitVec.ofNat 64 ((ph (x_3) (y_4) + pl (x_4) (y_4)))),
      .value (BitVec.ofNat 64 ((ph (x_3) (y_5) + pl (x_4) (y_5)))), .value (BitVec.ofNat 64 (0)),
      .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)),
      .poison, .poison]
  have v126Value : v126 = q4j := by mul_shuffle hv126
  subst v126Value
  let p5j :=
    toBitVecValue 64
      #v[0, 0, 0, 0, 0, (ph (x_4) (y_0) + pl (x_5) (y_0)), (ph (x_4) (y_1) + pl (x_5) (y_1)),
        (ph (x_4) (y_2) + pl (x_5) (y_2))]
  have v127Value : v127 = p5j := by mul_shuffle hv127
  subst v127Value
  let q5j : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[.value (BitVec.ofNat 64 ((ph (x_4) (y_3) + pl (x_5) (y_3)))),
      .value (BitVec.ofNat 64 ((ph (x_4) (y_4) + pl (x_5) (y_4)))),
      .value (BitVec.ofNat 64 ((ph (x_4) (y_5) + pl (x_5) (y_5)))), .value (BitVec.ofNat 64 (0)),
      .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v128Value : v128 = q5j := by mul_shuffle hv128
  subst v128Value
  let p6j := toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, ph (x_5) (y_0), ph (x_5) (y_1)]
  have v129Value : v129 = p6j := by mul_shuffle hv129
  subst v129Value
  let q6j : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[.value (BitVec.ofNat 64 (ph (x_5) (y_2))), .value (BitVec.ofNat 64 (ph (x_5) (y_3))),
      .value (BitVec.ofNat 64 (ph (x_5) (y_4))), .value (BitVec.ofNat 64 (ph (x_5) (y_5))),
      .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v130Value : v130 = q6j := by mul_shuffle hv130
  subst v130Value
  denote_clear v 121 130
  -- `%131`-`%136` = `zl`, `%137`-`%139` = `zh`: the big adds.
  denote_step_all v 139
  let zlAcc1 :=
    toBitVecValue 64
      #v[0 + pl (x_0) (y_0), (ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1),
        (ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2),
        (ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3),
        (ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4),
        (ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5), (ph (x_0) (y_5) + pl (x_1) (y_5)) + 0,
        0 + 0]
  have v131Value : v131 = zlAcc1 := by denote_vecbin hv131
  subst v131Value
  let zlAcc2 :=
    toBitVecValue 64
      #v[(0 + pl (x_0) (y_0)) + 0, ((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0,
        ((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0)),
        ((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1)),
        ((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2)),
        ((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3)),
        ((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4)),
        (0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))]
  have v132Value : v132 = zlAcc2 := by denote_vecbin hv132
  subst v132Value
  let zlAcc3 :=
    toBitVecValue 64
      #v[((0 + pl (x_0) (y_0)) + 0) + 0,
        (((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0,
        (((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0))) +
          0,
        (((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1))) +
          (ph (x_2) (y_0) + pl (x_3) (y_0)),
        (((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2))) +
          (ph (x_2) (y_1) + pl (x_3) (y_1)),
        (((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3))) +
          (ph (x_2) (y_2) + pl (x_3) (y_2)),
        (((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
          (ph (x_2) (y_3) + pl (x_3) (y_3)),
        ((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))]
  have v133Value : v133 = zlAcc3 := by denote_vecbin hv133
  subst v133Value
  let zlAcc4 :=
    toBitVecValue 64
      #v[(((0 + pl (x_0) (y_0)) + 0) + 0) + 0,
        ((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0,
        ((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) +
              (ph (x_1) (y_0) + pl (x_2) (y_0))) +
            0) +
          0,
        ((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) +
              (ph (x_1) (y_1) + pl (x_2) (y_1))) +
            (ph (x_2) (y_0) + pl (x_3) (y_0))) +
          0,
        ((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) +
              (ph (x_1) (y_2) + pl (x_2) (y_2))) +
            (ph (x_2) (y_1) + pl (x_3) (y_1))) +
          (ph (x_3) (y_0) + pl (x_4) (y_0)),
        ((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) +
              (ph (x_1) (y_3) + pl (x_2) (y_3))) +
            (ph (x_2) (y_2) + pl (x_3) (y_2))) +
          (ph (x_3) (y_1) + pl (x_4) (y_1)),
        ((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
            (ph (x_2) (y_3) + pl (x_3) (y_3))) +
          (ph (x_3) (y_2) + pl (x_4) (y_2)),
        (((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) +
          (ph (x_3) (y_3) + pl (x_4) (y_3))]
  have v134Value : v134 = zlAcc4 := by denote_vecbin hv134
  subst v134Value
  let zlAcc5 :=
    toBitVecValue 64
      #v[((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0,
        (((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0,
        (((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) +
                (ph (x_1) (y_0) + pl (x_2) (y_0))) +
              0) +
            0) +
          0,
        (((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) +
                (ph (x_1) (y_1) + pl (x_2) (y_1))) +
              (ph (x_2) (y_0) + pl (x_3) (y_0))) +
            0) +
          0,
        (((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) +
                (ph (x_1) (y_2) + pl (x_2) (y_2))) +
              (ph (x_2) (y_1) + pl (x_3) (y_1))) +
            (ph (x_3) (y_0) + pl (x_4) (y_0))) +
          0,
        (((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) +
                (ph (x_1) (y_3) + pl (x_2) (y_3))) +
              (ph (x_2) (y_2) + pl (x_3) (y_2))) +
            (ph (x_3) (y_1) + pl (x_4) (y_1))) +
          (ph (x_4) (y_0) + pl (x_5) (y_0)),
        (((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
              (ph (x_2) (y_3) + pl (x_3) (y_3))) +
            (ph (x_3) (y_2) + pl (x_4) (y_2))) +
          (ph (x_4) (y_1) + pl (x_5) (y_1)),
        ((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) +
            (ph (x_3) (y_3) + pl (x_4) (y_3))) +
          (ph (x_4) (y_2) + pl (x_5) (y_2))]
  have v135Value : v135 = zlAcc5 := by denote_vecbin hv135
  subst v135Value
  let zl :=
    toBitVecValue 64
      #v[(((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0) + 0,
        ((((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0) + 0,
        ((((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) +
                  (ph (x_1) (y_0) + pl (x_2) (y_0))) +
                0) +
              0) +
            0) +
          0,
        ((((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) +
                  (ph (x_1) (y_1) + pl (x_2) (y_1))) +
                (ph (x_2) (y_0) + pl (x_3) (y_0))) +
              0) +
            0) +
          0,
        ((((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) +
                  (ph (x_1) (y_2) + pl (x_2) (y_2))) +
                (ph (x_2) (y_1) + pl (x_3) (y_1))) +
              (ph (x_3) (y_0) + pl (x_4) (y_0))) +
            0) +
          0,
        ((((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) +
                  (ph (x_1) (y_3) + pl (x_2) (y_3))) +
                (ph (x_2) (y_2) + pl (x_3) (y_2))) +
              (ph (x_3) (y_1) + pl (x_4) (y_1))) +
            (ph (x_4) (y_0) + pl (x_5) (y_0))) +
          0,
        ((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
                (ph (x_2) (y_3) + pl (x_3) (y_3))) +
              (ph (x_3) (y_2) + pl (x_4) (y_2))) +
            (ph (x_4) (y_1) + pl (x_5) (y_1))) +
          ph (x_5) (y_0),
        (((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) +
              (ph (x_3) (y_3) + pl (x_4) (y_3))) +
            (ph (x_4) (y_2) + pl (x_5) (y_2))) +
          ph (x_5) (y_1)]
  have v136Value : v136 = zl := by denote_vecbin hv136
  subst v136Value
  let zhAcc1 : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[.value
        (BitVec.ofNat 64 ((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5)))),
      .value (BitVec.ofNat 64 ((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0)),
      .value (BitVec.ofNat 64 (0 + 0)), .value (BitVec.ofNat 64 (0 + 0)),
      .value (BitVec.ofNat 64 (0 + 0)), .value (BitVec.ofNat 64 (0 + 0)), .poison, .poison]
  have v137Value : v137 = zhAcc1 := by denote_vecbin hv137
  subst v137Value
  let zhAcc2 : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[.value
        (BitVec.ofNat 64
          (((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) +
            (ph (x_4) (y_3) + pl (x_5) (y_3)))),
      .value
        (BitVec.ofNat 64
          (((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4)))),
      .value (BitVec.ofNat 64 ((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5)))),
      .value (BitVec.ofNat 64 ((0 + 0) + 0)), .value (BitVec.ofNat 64 ((0 + 0) + 0)),
      .value (BitVec.ofNat 64 ((0 + 0) + 0)), .poison, .poison]
  have v138Value : v138 = zhAcc2 := by denote_vecbin hv138
  subst v138Value
  let zh : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[.value
        (BitVec.ofNat 64
          ((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) +
              (ph (x_4) (y_3) + pl (x_5) (y_3))) +
            ph (x_5) (y_2))),
      .value
        (BitVec.ofNat 64
          ((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) +
            ph (x_5) (y_3))),
      .value (BitVec.ofNat 64 (((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4))),
      .value (BitVec.ofNat 64 (((0 + 0) + 0) + ph (x_5) (y_5))),
      .value (BitVec.ofNat 64 (((0 + 0) + 0) + 0)), .value (BitVec.ofNat 64 (((0 + 0) + 0) + 0)),
      .poison, .poison]
  have v139Value : v139 = zh := by denote_vecbin hv139
  subst v139Value
  denote_clear v 131 139
  -- `%140` = `za`, `%141` = `zb`, `%142`-`%145`: the final fold.
  denote_step_all v 145
  let za :=
    toBitVecValue 64
      #v[(((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0) + 0,
        ((((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0) + 0,
        ((((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) +
                  (ph (x_1) (y_0) + pl (x_2) (y_0))) +
                0) +
              0) +
            0) +
          0,
        ((((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) +
                  (ph (x_1) (y_1) + pl (x_2) (y_1))) +
                (ph (x_2) (y_0) + pl (x_3) (y_0))) +
              0) +
            0) +
          0,
        ((((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) +
                  (ph (x_1) (y_2) + pl (x_2) (y_2))) +
                (ph (x_2) (y_1) + pl (x_3) (y_1))) +
              (ph (x_3) (y_0) + pl (x_4) (y_0))) +
            0) +
          0,
        ((((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) +
                  (ph (x_1) (y_3) + pl (x_2) (y_3))) +
                (ph (x_2) (y_2) + pl (x_3) (y_2))) +
              (ph (x_3) (y_1) + pl (x_4) (y_1))) +
            (ph (x_4) (y_0) + pl (x_5) (y_0))) +
          0,
        0, 0]
  have v140Value : v140 = za := by denote_vecbin hv140
  subst v140Value
  let zb :=
    toBitVecValue 64
      #v[((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
                (ph (x_2) (y_3) + pl (x_3) (y_3))) +
              (ph (x_3) (y_2) + pl (x_4) (y_2))) +
            (ph (x_4) (y_1) + pl (x_5) (y_1))) +
          ph (x_5) (y_0),
        (((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) +
              (ph (x_3) (y_3) + pl (x_4) (y_3))) +
            (ph (x_4) (y_2) + pl (x_5) (y_2))) +
          ph (x_5) (y_1),
        (((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) +
            (ph (x_4) (y_3) + pl (x_5) (y_3))) +
          ph (x_5) (y_2),
        (((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) +
          ph (x_5) (y_3),
        ((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4),
        ((0 + 0) + 0) + ph (x_5) (y_5), ((0 + 0) + 0) + 0, ((0 + 0) + 0) + 0]
  have v141Value : v141 = zb := by mul_shuffle hv141
  subst v141Value
  let zbShl7 :=
    toBitVecValue 64
      #v[(((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
                  (ph (x_2) (y_3) + pl (x_3) (y_3))) +
                (ph (x_3) (y_2) + pl (x_4) (y_2))) +
              (ph (x_4) (y_1) + pl (x_5) (y_1))) +
            ph (x_5) (y_0)) *
          128,
        ((((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) +
                (ph (x_3) (y_3) + pl (x_4) (y_3))) +
              (ph (x_4) (y_2) + pl (x_5) (y_2))) +
            ph (x_5) (y_1)) *
          128,
        ((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) +
              (ph (x_4) (y_3) + pl (x_5) (y_3))) +
            ph (x_5) (y_2)) *
          128,
        ((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) +
            ph (x_5) (y_3)) *
          128,
        (((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4)) * 128,
        (((0 + 0) + 0) + ph (x_5) (y_5)) * 128, (((0 + 0) + 0) + 0) * 128,
        (((0 + 0) + 0) + 0) * 128]
  have v142Value : v142 = zbShl7 := by denote_vecbin hv142
  subst v142Value
  let zbShl7Za :=
    toBitVecValue 64
      #v[((((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
                    (ph (x_2) (y_3) + pl (x_3) (y_3))) +
                  (ph (x_3) (y_2) + pl (x_4) (y_2))) +
                (ph (x_4) (y_1) + pl (x_5) (y_1))) +
              ph (x_5) (y_0)) *
            128) +
          ((((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0) + 0),
        (((((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) +
                  (ph (x_3) (y_3) + pl (x_4) (y_3))) +
                (ph (x_4) (y_2) + pl (x_5) (y_2))) +
              ph (x_5) (y_1)) *
            128) +
          (((((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0) + 0),
        (((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) +
                (ph (x_4) (y_3) + pl (x_5) (y_3))) +
              ph (x_5) (y_2)) *
            128) +
          (((((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) +
                    (ph (x_1) (y_0) + pl (x_2) (y_0))) +
                  0) +
                0) +
              0) +
            0),
        (((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) +
              ph (x_5) (y_3)) *
            128) +
          (((((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) +
                    (ph (x_1) (y_1) + pl (x_2) (y_1))) +
                  (ph (x_2) (y_0) + pl (x_3) (y_0))) +
                0) +
              0) +
            0),
        ((((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4)) * 128) +
          (((((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) +
                    (ph (x_1) (y_2) + pl (x_2) (y_2))) +
                  (ph (x_2) (y_1) + pl (x_3) (y_1))) +
                (ph (x_3) (y_0) + pl (x_4) (y_0))) +
              0) +
            0),
        ((((0 + 0) + 0) + ph (x_5) (y_5)) * 128) +
          (((((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) +
                    (ph (x_1) (y_3) + pl (x_2) (y_3))) +
                  (ph (x_2) (y_2) + pl (x_3) (y_2))) +
                (ph (x_3) (y_1) + pl (x_4) (y_1))) +
              (ph (x_4) (y_0) + pl (x_5) (y_0))) +
            0),
        ((((0 + 0) + 0) + 0) * 128) + (0), ((((0 + 0) + 0) + 0) * 128) + (0)]
  have v143Value : v143 = zbShl7Za := by denote_vecbin hv143
  let zbMul24 :=
    toBitVecValue 64
      #v[(((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) +
                  (ph (x_2) (y_3) + pl (x_3) (y_3))) +
                (ph (x_3) (y_2) + pl (x_4) (y_2))) +
              (ph (x_4) (y_1) + pl (x_5) (y_1))) +
            ph (x_5) (y_0)) *
          24,
        ((((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) +
                (ph (x_3) (y_3) + pl (x_4) (y_3))) +
              (ph (x_4) (y_2) + pl (x_5) (y_2))) +
            ph (x_5) (y_1)) *
          24,
        ((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) +
              (ph (x_4) (y_3) + pl (x_5) (y_3))) +
            ph (x_5) (y_2)) *
          24,
        ((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) +
            ph (x_5) (y_3)) *
          24,
        (((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4)) * 24,
        (((0 + 0) + 0) + ph (x_5) (y_5)) * 24, (((0 + 0) + 0) + 0) * 24, (((0 + 0) + 0) + 0) * 24]
  have v144Value : v144 = zbMul24 := by denote_vecbin hv144
  subst v143Value v144Value
  -- `%145`: the final add, against the specified limbs: `vec8_add`, then per
  -- lane `limb`/`col` and `ring` over folded `ph`/`pl` (`152 = 128 + 24`).
  have v145Value : v145 = (mulVec x y).map PoisonOr.value := by
    simp only [hv145, Expr.denoteOp1, Expr.denoteOpPure]
    simp_denote_only
    simp only [HVector.head]
    refine (vec8_add _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
    apply Vector.ext
    intro i hi
    interval_cases i <;>
      simp only [toBitVecValue, mulVec, limbVec, Vector.getElem_map, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] <;>
      (try congr 2) <;>
      (try simp +zetaDelta only [limb, col, Fin.reduceCastAdd, Fin.reduceAddNat]) <;>
      ring
  subst v145Value
  simp_denote_only

abbrev mulValue (x y : Vector (BitVec 64) 8) :=
  (fd_r43x6_mul_fast.denote
      (Ctxt.Valuation.ofPair (y.map PoisonOr.value) (x.map PoisonOr.value))).head.getValues

abbrev mulIsMul (x y : Vector (BitVec 64) 8) :=
  (fun l => (R43x6.decode' l : ZMod p)) <$> mulValue x y =
    .value ((R43x6.decode' x : ZMod p) * (R43x6.decode' y : ZMod p))

def output_bounds_u44_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U44 x → R43x6.U44 y → R43x6.U62 (mulValue x y).getValue

def output_bounds_u45_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U45 x → R43x6.U45 y → R43x6.U62 (mulValue x y).getValue

def output_bounds_u46_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U46 x → R43x6.U46 y → R43x6.U62 (mulValue x y).getValue

def output_bounds_u47_u63 (x y : Vector (BitVec 64) 8) :=
  R43x6.U47 x → R43x6.U47 y → R43x6.U63 (mulValue x y).getValue

set_option maxHeartbeats 1000000 in
private theorem mulIsMulThm (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) : mulIsMul x y := by
  have hbx : ∀ i : Fin 6, limbNat x i < 2 ^ 47 := limbNat_lt x 47 (by omega) hx
  have hby : ∀ i : Fin 6, limbNat y i < 2 ^ 47 := limbNat_lt y 47 (by omega) hy
  -- 1. denotation to lanes to specified limbs; the poison layer collapses
  rw [mulIsMul, mulValue, denote_fd_r43x6_mul_fast x y hx hy hy6 hy7]
  simp only [HVector.head, Vector.getValues_map_value, PoisonOr.map_value, PoisonOr.value_inj]
  -- 2. decode both sides into casts of `decodeNat`
  have hdecode :
    ∀ (v : Vector (BitVec 64) 8),
      R43x6.Unreduced v → R43x6.decode' v = ((decodeNat (limbNat v) : ℕ) : Int) := by
    intro v hv
    have hv8 : v = #v[v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]] := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    have hb : ∀ i : Fin 6, limbNat v i < 2 ^ 47 := limbNat_lt v 47 (by omega) hv
    conv_lhs => rw [hv8]
    rw [decode'_lit, toInt_of_lt (by simpa [limbNat] using hb 0),
      toInt_of_lt (by simpa [limbNat] using hb 1), toInt_of_lt (by simpa [limbNat] using hb 2),
      toInt_of_lt (by simpa [limbNat] using hb 3), toInt_of_lt (by simpa [limbNat] using hb 4),
      toInt_of_lt (by simpa [limbNat] using hb 5)]
    push_cast [decodeNat_eq, limbNat]
    try ring
  rw [mulVec, decode'_limbVec _ (limb_lt_two_pow_63 _ _ hbx hby), hdecode x hx, hdecode y hy]
  -- 3. both sides are now casts of `decodeNat`, so `decodeLimbs_limb_zmod` applies
  push_cast
  exact decodeLimbs_limb_zmod (limbNat x) (limbNat y)

/-! ## Output bounds

The four rows of the `fd_r43x6.h` table, each `limb_lt_u4x` transported
through the denotation: output lane `k < 6` is the specified limb, lanes 6
and 7 are zero, and none is read back as negative. -/

/-- The program's result, with the poison layer discharged. -/
private theorem mulValue_eq (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulValue x y = .value (mulVec x y) := by
  rw [mulValue, denote_fd_r43x6_mul_fast x y hx hy hy6 hy7]
  simp only [HVector.head, Vector.getValues_map_value]

/-- Two-sided lane bounds from a ceiling `N` on the ℕ-level limbs. -/
private theorem output_bounds_of (x y : Vector (BitVec 64) 8) (N : ℕ) (hN : N ≤ 2 ^ 63)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0)
    (hb : ∀ k, limb (limbNat x) (limbNat y) k < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (mulValue x y).getValue ∧
      R43x6.BoundedLower 0 (mulValue x y).getValue := by
  have hv : (mulValue x y).getValue = mulVec x y := by
    rw [mulValue_eq x y hx hy hy6 hy7]; rfl
  rw [hv, mulVec]
  exact limbVec_bounds _ N hN hb

private theorem output_u44 (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u44_u62 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2 ^ 62 := fun k =>
    limb_lt_u44 _ _ (limbNat_lt x 44 (by omega) hinx) (limbNat_lt y 44 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2 ^ 62) (by omega) hx hy hy6 hy7 hb

private theorem output_u45 (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u45_u62 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2 ^ 62 := fun k =>
    limb_lt_u45 _ _ (limbNat_lt x 45 (by omega) hinx) (limbNat_lt y 45 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2 ^ 62) (by omega) hx hy hy6 hy7 hb

private theorem output_u46 (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u46_u62 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2 ^ 62 := fun k =>
    limb_lt_u46 _ _ (limbNat_lt x 46 (by omega) hinx) (limbNat_lt y 46 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2 ^ 62) (by omega) hx hy hy6 hy7 hb

private theorem output_u47 (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u47_u63 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2 ^ 63 := fun k =>
    limb_lt_u47 _ _ (limbNat_lt x 47 (by omega) hinx) (limbNat_lt y 47 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2 ^ 63) (by omega) hx hy hy6 hy7 hb

/-- **Specification of `fd_r43x6_mul_fast`**: on unreduced inputs whose `y`
high lanes are zero, the six output limbs decode to the product of the decoded
inputs in `GF(2^255 - 19)`, and the four input/output width guarantees of
`fd_r43x6.h` hold. -/
theorem spec_fd_r43x6_mul_fast (x y : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x)
    (hy : R43x6.Unreduced y) (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulIsMul x y ∧
      output_bounds_u44_u62 x y ∧
      output_bounds_u45_u62 x y ∧ output_bounds_u46_u62 x y ∧ output_bounds_u47_u63 x y :=
  ⟨mulIsMulThm x y hx hy hy6 hy7, output_u44 x y hx hy hy6 hy7, output_u45 x y hx hy hy6 hy7,
    output_u46 x y hx hy hy6 hy7, output_u47 x y hx hy hy6 hy7⟩

end Firedancer.Avx512

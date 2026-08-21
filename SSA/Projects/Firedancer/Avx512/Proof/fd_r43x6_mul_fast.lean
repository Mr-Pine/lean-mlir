/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: the bulk of this file was machine-generated; the structure mirrors
the data flow of `fd_r43x6_mul_fast`.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.MLIR.Poison
import SSA.Projects.Firedancer.Ed25519

/-!
# `fd_r43x6_mul_fast` multiplies in `ZMod p`

Denoting the lifted SLLVM program and decoding the six output limbs yields the
product of the decoded inputs in `GF(2^255 - 19)`, within the widths the
`fd_r43x6.h` table promises.

The derivation runs at the N level throughout: each of the 209 instructions is
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

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! The bound facts the per-opcode tactics need, bound once here rather than at
each of the instructions that needs them. `Lean.mkIdent` escapes macro hygiene
so these refer to the `have`s of the theorem below, which the generated body
names by convention. -/

local macro "mul_shuffle " h:term : tactic =>
  `(tactic| denote_shuffle $h with
      $(Lean.mkIdent `hy6):ident, $(Lean.mkIdent `hy7):ident)

local macro "mul_vpmadd52 " h:term : tactic =>
  `(tactic| denote_vpmadd52 $h with
      $(Lean.mkIdent `hy6):ident, $(Lean.mkIdent `hy7):ident,
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
`mulVec x y` -- every one of the 209 instructions carried through at the N
level. -/
theorem denote_fd_r43x6_mul_fast (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    fd_r43x6_mul_fast.denote
        (Ctxt.Valuation.ofPair (y.map PoisonOr.value) (x.map PoisonOr.value)) =
      ([(mulVec x y).map PoisonOr.value]ₕ :
        HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))]) := by
  -- The operand bounds that make each `vpmadd52` truncation the identity.
  have bx0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0
  have bx1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1
  have bx2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2
  have bx3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3
  have bx4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4
  have bx5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5
  have by0 : y[0].toNat < 2^47 := unn_toNat y 47 (by omega) hy 0
  have by1 : y[1].toNat < 2^47 := unn_toNat y 47 (by omega) hy 1
  have by2 : y[2].toNat < 2^47 := unn_toNat y 47 (by omega) hy 2
  have by3 : y[3].toNat < 2^47 := unn_toNat y 47 (by omega) hy 3
  have by4 : y[4].toNat < 2^47 := unn_toNat y 47 (by omega) hy 4
  have by5 : y[5].toNat < 2^47 := unn_toNat y 47 (by omega) hy 5
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
  denote_step_all v 4
  let zeroBVP : PoisonOr (BitVec 64) := .value 0
  let neg1BVP : PoisonOr (BitVec 64) := .value (-1)
  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)
  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)
  have v1Zero : v1 = zeroBVP := by
    simp only [hv1, Expr.denoteOp1, Expr.denoteOpPure]
    simp_peephole
    simp only [HVector.head]
    rfl
  have v2Value : v2 = zeroVec := by denote_dense hv2
  have v3Value : v3 = nineVec := by denote_dense hv3
  have v4Poison : v4 = PoisonOr.poison := by
    simp only [hv4]
    simp_peephole
    rfl
  subst v1Zero v2Value v3Value v4Poison
  clear hv0 hv1 hv2 hv3 hv4

  -- The `wwl_slide` zero operands: an `undef` vector with zero written into
  -- the lanes each slide actually reads, the rest left poison.
  let p7z1 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 7 (PoisonOr.poison : PoisonOr (BitVec 64))).append (Vector.replicate 1 (.value (BitVec.zero 64)))
  denote_step_all v 21
  have v21Value : v21 = p7z1 := by
    denote_eval v 5 21
    denote_expand v 5 21
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v21Value
  denote_clear v 5 21

  let p6z2 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 6 (PoisonOr.poison : PoisonOr (BitVec 64))).append (Vector.replicate 2 (.value (BitVec.zero 64)))
  denote_step_all v 38
  have v38Value : v38 = p6z2 := by
    denote_eval v 22 38
    denote_expand v 22 38
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v38Value
  denote_clear v 22 38

  let p5z3 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 5 (PoisonOr.poison : PoisonOr (BitVec 64))).append (Vector.replicate 3 (.value (BitVec.zero 64)))
  denote_step_all v 55
  have v55Value : v55 = p5z3 := by
    denote_eval v 39 55
    denote_expand v 39 55
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v55Value
  denote_clear v 39 55

  let z3p5 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 3 (PoisonOr.value (BitVec.zero 64))).append (Vector.replicate 5 (.poison : PoisonOr (BitVec 64)))
  denote_step_all v 72
  have v72Value : v72 = z3p5 := by
    denote_eval v 56 72
    denote_expand v 56 72
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v72Value
  denote_clear v 56 72

  let p4z4 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 4 (PoisonOr.poison : PoisonOr (BitVec 64))).append (Vector.replicate 4 (.value (BitVec.zero 64)))
  denote_step_all v 89
  have v89Value : v89 = p4z4 := by
    denote_eval v 73 89
    denote_expand v 73 89
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v89Value
  denote_clear v 73 89

  let z2p6 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 2 (PoisonOr.value (BitVec.zero 64))).append (Vector.replicate 6 (.poison : PoisonOr (BitVec 64)))
  denote_step_all v 106
  have v106Value : v106 = z2p6 := by
    denote_eval v 90 106
    denote_expand v 90 106
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v106Value
  denote_clear v 90 106

  let p3z5 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 3 (PoisonOr.poison : PoisonOr (BitVec 64))).append (Vector.replicate 5 (.value (BitVec.zero 64)))
  denote_step_all v 123
  have v123Value : v123 = p3z5 := by
    denote_eval v 107 123
    denote_expand v 107 123
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v123Value
  denote_clear v 107 123

  let z1p7 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 1 (PoisonOr.value (BitVec.zero 64))).append (Vector.replicate 7 (.poison : PoisonOr (BitVec 64)))
  denote_step_all v 140
  have v140Value : v140 = z1p7 := by
    denote_eval v 124 140
    denote_expand v 124 140
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v140Value
  denote_clear v 124 140

  let p2z6 : Vector (PoisonOr (BitVec 64)) 8 := (Vector.replicate 2 (PoisonOr.poison : PoisonOr (BitVec 64))).append (Vector.replicate 6 (.value (BitVec.zero 64)))
  denote_step_all v 157
  have v157Value : v157 = p2z6 := by
    denote_eval v 141 157
    denote_expand v 141 157
    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]
    rfl
  subst v157Value
  denote_clear v 141 157

  -- `%158`-`%160`: the `za` mask and the fold constants.
  let zaMask : Vector (PoisonOr (BitVec 64)) 8 :=
    #v[neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, zeroBVP, zeroBVP]
  let dense7 := toBitVecValue 64 (Vector.replicate 8 7)
  let dense24 := toBitVecValue 64 (Vector.replicate 8 24)
  denote_step_all v 160
  have v158Value : v158 = zaMask := by denote_dense hv158
  have v159Value : v159 = dense7 := by denote_dense hv159
  have v160Value : v160 = dense24 := by denote_dense hv160
  subst v158Value v159Value v160Value
  denote_clear v 158 160

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

  -- `%161`-`%166` = `x0`-`x5`: `wwl_permute( wwl_bcast( iL ), x )`.
  denote_step_all v 166
  let xb0 := toBitVecValue 64 #v[x_0, x_0, x_0, x_0, x_0, x_0, x_0, x_0]
  let xb1 := toBitVecValue 64 #v[x_1, x_1, x_1, x_1, x_1, x_1, x_1, x_1]
  let xb2 := toBitVecValue 64 #v[x_2, x_2, x_2, x_2, x_2, x_2, x_2, x_2]
  let xb3 := toBitVecValue 64 #v[x_3, x_3, x_3, x_3, x_3, x_3, x_3, x_3]
  let xb4 := toBitVecValue 64 #v[x_4, x_4, x_4, x_4, x_4, x_4, x_4, x_4]
  let xb5 := toBitVecValue 64 #v[x_5, x_5, x_5, x_5, x_5, x_5, x_5, x_5]
  have v161Value : v161 = xb0 := by mul_shuffle hv161
  have v162Value : v162 = xb1 := by mul_shuffle hv162
  have v163Value : v163 = xb2 := by mul_shuffle hv163
  have v164Value : v164 = xb3 := by mul_shuffle hv164
  have v165Value : v165 = xb4 := by mul_shuffle hv165
  have v166Value : v166 = xb5 := by mul_shuffle hv166
  subst v161Value v162Value v163Value v164Value v165Value v166Value
  denote_clear v 161 166

  -- `%167`-`%184` = `t0`-`t6`: `t_i = wwl_madd52lo( wwl_shl( wwl_madd52hi( zero, x_(i-1), y ), 9 ), x_i, y )`.
  denote_step_all v 184
  let t0 := toBitVecValue 64 #v[pl (x_0) (y_0), pl (x_0) (y_1), pl (x_0) (y_2), pl (x_0) (y_3), pl (x_0) (y_4), pl (x_0) (y_5), 0, 0]
  have v167Value : v167 = t0 := by mul_vpmadd52 hv167
  subst v167Value
  let hi0 := toBitVecValue 64 #v[phRaw (x_0) (y_0), phRaw (x_0) (y_1), phRaw (x_0) (y_2), phRaw (x_0) (y_3), phRaw (x_0) (y_4), phRaw (x_0) (y_5), 0, 0]
  have v168Value : v168 = hi0 := by mul_vpmadd52 hv168
  subst v168Value
  let hs0 := toBitVecValue 64 #v[ph (x_0) (y_0), ph (x_0) (y_1), ph (x_0) (y_2), ph (x_0) (y_3), ph (x_0) (y_4), ph (x_0) (y_5), 0, 0]
  have v169Value : v169 = hs0 := by denote_vecbin hv169
  subst v169Value
  let t1 := toBitVecValue 64 #v[ph (x_0) (y_0) + pl (x_1) (y_0), ph (x_0) (y_1) + pl (x_1) (y_1), ph (x_0) (y_2) + pl (x_1) (y_2), ph (x_0) (y_3) + pl (x_1) (y_3), ph (x_0) (y_4) + pl (x_1) (y_4), ph (x_0) (y_5) + pl (x_1) (y_5), 0, 0]
  have v170Value : v170 = t1 := by mul_vpmadd52 hv170
  subst v170Value
  let hi1 := toBitVecValue 64 #v[phRaw (x_1) (y_0), phRaw (x_1) (y_1), phRaw (x_1) (y_2), phRaw (x_1) (y_3), phRaw (x_1) (y_4), phRaw (x_1) (y_5), 0, 0]
  have v171Value : v171 = hi1 := by mul_vpmadd52 hv171
  subst v171Value
  let hs1 := toBitVecValue 64 #v[ph (x_1) (y_0), ph (x_1) (y_1), ph (x_1) (y_2), ph (x_1) (y_3), ph (x_1) (y_4), ph (x_1) (y_5), 0, 0]
  have v172Value : v172 = hs1 := by denote_vecbin hv172
  subst v172Value
  let t2 := toBitVecValue 64 #v[ph (x_1) (y_0) + pl (x_2) (y_0), ph (x_1) (y_1) + pl (x_2) (y_1), ph (x_1) (y_2) + pl (x_2) (y_2), ph (x_1) (y_3) + pl (x_2) (y_3), ph (x_1) (y_4) + pl (x_2) (y_4), ph (x_1) (y_5) + pl (x_2) (y_5), 0, 0]
  have v173Value : v173 = t2 := by mul_vpmadd52 hv173
  subst v173Value
  let hi2 := toBitVecValue 64 #v[phRaw (x_2) (y_0), phRaw (x_2) (y_1), phRaw (x_2) (y_2), phRaw (x_2) (y_3), phRaw (x_2) (y_4), phRaw (x_2) (y_5), 0, 0]
  have v174Value : v174 = hi2 := by mul_vpmadd52 hv174
  subst v174Value
  let hs2 := toBitVecValue 64 #v[ph (x_2) (y_0), ph (x_2) (y_1), ph (x_2) (y_2), ph (x_2) (y_3), ph (x_2) (y_4), ph (x_2) (y_5), 0, 0]
  have v175Value : v175 = hs2 := by denote_vecbin hv175
  subst v175Value
  let t3 := toBitVecValue 64 #v[ph (x_2) (y_0) + pl (x_3) (y_0), ph (x_2) (y_1) + pl (x_3) (y_1), ph (x_2) (y_2) + pl (x_3) (y_2), ph (x_2) (y_3) + pl (x_3) (y_3), ph (x_2) (y_4) + pl (x_3) (y_4), ph (x_2) (y_5) + pl (x_3) (y_5), 0, 0]
  have v176Value : v176 = t3 := by mul_vpmadd52 hv176
  subst v176Value
  let hi3 := toBitVecValue 64 #v[phRaw (x_3) (y_0), phRaw (x_3) (y_1), phRaw (x_3) (y_2), phRaw (x_3) (y_3), phRaw (x_3) (y_4), phRaw (x_3) (y_5), 0, 0]
  have v177Value : v177 = hi3 := by mul_vpmadd52 hv177
  subst v177Value
  let hs3 := toBitVecValue 64 #v[ph (x_3) (y_0), ph (x_3) (y_1), ph (x_3) (y_2), ph (x_3) (y_3), ph (x_3) (y_4), ph (x_3) (y_5), 0, 0]
  have v178Value : v178 = hs3 := by denote_vecbin hv178
  subst v178Value
  let t4 := toBitVecValue 64 #v[ph (x_3) (y_0) + pl (x_4) (y_0), ph (x_3) (y_1) + pl (x_4) (y_1), ph (x_3) (y_2) + pl (x_4) (y_2), ph (x_3) (y_3) + pl (x_4) (y_3), ph (x_3) (y_4) + pl (x_4) (y_4), ph (x_3) (y_5) + pl (x_4) (y_5), 0, 0]
  have v179Value : v179 = t4 := by mul_vpmadd52 hv179
  subst v179Value
  let hi4 := toBitVecValue 64 #v[phRaw (x_4) (y_0), phRaw (x_4) (y_1), phRaw (x_4) (y_2), phRaw (x_4) (y_3), phRaw (x_4) (y_4), phRaw (x_4) (y_5), 0, 0]
  have v180Value : v180 = hi4 := by mul_vpmadd52 hv180
  subst v180Value
  let hs4 := toBitVecValue 64 #v[ph (x_4) (y_0), ph (x_4) (y_1), ph (x_4) (y_2), ph (x_4) (y_3), ph (x_4) (y_4), ph (x_4) (y_5), 0, 0]
  have v181Value : v181 = hs4 := by denote_vecbin hv181
  subst v181Value
  let t5 := toBitVecValue 64 #v[ph (x_4) (y_0) + pl (x_5) (y_0), ph (x_4) (y_1) + pl (x_5) (y_1), ph (x_4) (y_2) + pl (x_5) (y_2), ph (x_4) (y_3) + pl (x_5) (y_3), ph (x_4) (y_4) + pl (x_5) (y_4), ph (x_4) (y_5) + pl (x_5) (y_5), 0, 0]
  have v182Value : v182 = t5 := by mul_vpmadd52 hv182
  subst v182Value
  let hi5 := toBitVecValue 64 #v[phRaw (x_5) (y_0), phRaw (x_5) (y_1), phRaw (x_5) (y_2), phRaw (x_5) (y_3), phRaw (x_5) (y_4), phRaw (x_5) (y_5), 0, 0]
  have v183Value : v183 = hi5 := by mul_vpmadd52 hv183
  subst v183Value
  let t6 := toBitVecValue 64 #v[ph (x_5) (y_0), ph (x_5) (y_1), ph (x_5) (y_2), ph (x_5) (y_3), ph (x_5) (y_4), ph (x_5) (y_5), 0, 0]
  have v184Value : v184 = t6 := by denote_vecbin hv184
  subst v184Value
  denote_clear v 167 184

  -- `%185`-`%194`: the `wwl_slide` shuffles `p1j`-`p6j` and `q3j`-`q6j`.
  denote_step_all v 194
  let p1j := toBitVecValue 64 #v[0, (ph (x_0) (y_0) + pl (x_1) (y_0)), (ph (x_0) (y_1) + pl (x_1) (y_1)), (ph (x_0) (y_2) + pl (x_1) (y_2)), (ph (x_0) (y_3) + pl (x_1) (y_3)), (ph (x_0) (y_4) + pl (x_1) (y_4)), (ph (x_0) (y_5) + pl (x_1) (y_5)), 0]
  have v185Value : v185 = p1j := by mul_shuffle hv185
  subst v185Value
  let p2j := toBitVecValue 64 #v[0, 0, (ph (x_1) (y_0) + pl (x_2) (y_0)), (ph (x_1) (y_1) + pl (x_2) (y_1)), (ph (x_1) (y_2) + pl (x_2) (y_2)), (ph (x_1) (y_3) + pl (x_2) (y_3)), (ph (x_1) (y_4) + pl (x_2) (y_4)), (ph (x_1) (y_5) + pl (x_2) (y_5))]
  have v186Value : v186 = p2j := by mul_shuffle hv186
  subst v186Value
  let p3j := toBitVecValue 64 #v[0, 0, 0, (ph (x_2) (y_0) + pl (x_3) (y_0)), (ph (x_2) (y_1) + pl (x_3) (y_1)), (ph (x_2) (y_2) + pl (x_3) (y_2)), (ph (x_2) (y_3) + pl (x_3) (y_3)), (ph (x_2) (y_4) + pl (x_3) (y_4))]
  have v187Value : v187 = p3j := by mul_shuffle hv187
  subst v187Value
  let q3j : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 ((ph (x_2) (y_5) + pl (x_3) (y_5)))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v188Value : v188 = q3j := by mul_shuffle hv188
  subst v188Value
  let p4j := toBitVecValue 64 #v[0, 0, 0, 0, (ph (x_3) (y_0) + pl (x_4) (y_0)), (ph (x_3) (y_1) + pl (x_4) (y_1)), (ph (x_3) (y_2) + pl (x_4) (y_2)), (ph (x_3) (y_3) + pl (x_4) (y_3))]
  have v189Value : v189 = p4j := by mul_shuffle hv189
  subst v189Value
  let q4j : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 ((ph (x_3) (y_4) + pl (x_4) (y_4)))), .value (BitVec.ofNat 64 ((ph (x_3) (y_5) + pl (x_4) (y_5)))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v190Value : v190 = q4j := by mul_shuffle hv190
  subst v190Value
  let p5j := toBitVecValue 64 #v[0, 0, 0, 0, 0, (ph (x_4) (y_0) + pl (x_5) (y_0)), (ph (x_4) (y_1) + pl (x_5) (y_1)), (ph (x_4) (y_2) + pl (x_5) (y_2))]
  have v191Value : v191 = p5j := by mul_shuffle hv191
  subst v191Value
  let q5j : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 ((ph (x_4) (y_3) + pl (x_5) (y_3)))), .value (BitVec.ofNat 64 ((ph (x_4) (y_4) + pl (x_5) (y_4)))), .value (BitVec.ofNat 64 ((ph (x_4) (y_5) + pl (x_5) (y_5)))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v192Value : v192 = q5j := by mul_shuffle hv192
  subst v192Value
  let p6j := toBitVecValue 64 #v[0, 0, 0, 0, 0, 0, ph (x_5) (y_0), ph (x_5) (y_1)]
  have v193Value : v193 = p6j := by mul_shuffle hv193
  subst v193Value
  let q6j : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (ph (x_5) (y_2))), .value (BitVec.ofNat 64 (ph (x_5) (y_3))), .value (BitVec.ofNat 64 (ph (x_5) (y_4))), .value (BitVec.ofNat 64 (ph (x_5) (y_5))), .value (BitVec.ofNat 64 (0)), .value (BitVec.ofNat 64 (0)), .poison, .poison]
  have v194Value : v194 = q6j := by mul_shuffle hv194
  subst v194Value
  denote_clear v 185 194

  -- `%195`-`%200` = `zl`, `%201`-`%203` = `zh`: the big adds.
  denote_step_all v 203
  let zlAcc1 := toBitVecValue 64 #v[0 + pl (x_0) (y_0), (ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1), (ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2), (ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3), (ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4), (ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5), (ph (x_0) (y_5) + pl (x_1) (y_5)) + 0, 0 + 0]
  have v195Value : v195 = zlAcc1 := by denote_vecbin hv195
  subst v195Value
  let zlAcc2 := toBitVecValue 64 #v[(0 + pl (x_0) (y_0)) + 0, ((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0, ((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0)), ((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1)), ((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2)), ((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3)), ((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4)), (0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))]
  have v196Value : v196 = zlAcc2 := by denote_vecbin hv196
  subst v196Value
  let zlAcc3 := toBitVecValue 64 #v[((0 + pl (x_0) (y_0)) + 0) + 0, (((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0, (((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0))) + 0, (((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1))) + (ph (x_2) (y_0) + pl (x_3) (y_0)), (((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2))) + (ph (x_2) (y_1) + pl (x_3) (y_1)), (((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3))) + (ph (x_2) (y_2) + pl (x_3) (y_2)), (((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3)), ((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))]
  have v197Value : v197 = zlAcc3 := by denote_vecbin hv197
  subst v197Value
  let zlAcc4 := toBitVecValue 64 #v[(((0 + pl (x_0) (y_0)) + 0) + 0) + 0, ((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0, ((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0))) + 0) + 0, ((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1))) + (ph (x_2) (y_0) + pl (x_3) (y_0))) + 0, ((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2))) + (ph (x_2) (y_1) + pl (x_3) (y_1))) + (ph (x_3) (y_0) + pl (x_4) (y_0)), ((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3))) + (ph (x_2) (y_2) + pl (x_3) (y_2))) + (ph (x_3) (y_1) + pl (x_4) (y_1)), ((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3))) + (ph (x_3) (y_2) + pl (x_4) (y_2)), (((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) + (ph (x_3) (y_3) + pl (x_4) (y_3))]
  have v198Value : v198 = zlAcc4 := by denote_vecbin hv198
  subst v198Value
  let zlAcc5 := toBitVecValue 64 #v[((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0, (((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0, (((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0))) + 0) + 0) + 0, (((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1))) + (ph (x_2) (y_0) + pl (x_3) (y_0))) + 0) + 0, (((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2))) + (ph (x_2) (y_1) + pl (x_3) (y_1))) + (ph (x_3) (y_0) + pl (x_4) (y_0))) + 0, (((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3))) + (ph (x_2) (y_2) + pl (x_3) (y_2))) + (ph (x_3) (y_1) + pl (x_4) (y_1))) + (ph (x_4) (y_0) + pl (x_5) (y_0)), (((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3))) + (ph (x_3) (y_2) + pl (x_4) (y_2))) + (ph (x_4) (y_1) + pl (x_5) (y_1)), ((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) + (ph (x_3) (y_3) + pl (x_4) (y_3))) + (ph (x_4) (y_2) + pl (x_5) (y_2))]
  have v199Value : v199 = zlAcc5 := by denote_vecbin hv199
  subst v199Value
  let zl := toBitVecValue 64 #v[(((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0) + 0, ((((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0) + 0, ((((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0))) + 0) + 0) + 0) + 0, ((((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1))) + (ph (x_2) (y_0) + pl (x_3) (y_0))) + 0) + 0) + 0, ((((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2))) + (ph (x_2) (y_1) + pl (x_3) (y_1))) + (ph (x_3) (y_0) + pl (x_4) (y_0))) + 0) + 0, ((((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3))) + (ph (x_2) (y_2) + pl (x_3) (y_2))) + (ph (x_3) (y_1) + pl (x_4) (y_1))) + (ph (x_4) (y_0) + pl (x_5) (y_0))) + 0, ((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3))) + (ph (x_3) (y_2) + pl (x_4) (y_2))) + (ph (x_4) (y_1) + pl (x_5) (y_1))) + ph (x_5) (y_0), (((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) + (ph (x_3) (y_3) + pl (x_4) (y_3))) + (ph (x_4) (y_2) + pl (x_5) (y_2))) + ph (x_5) (y_1)]
  have v200Value : v200 = zl := by denote_vecbin hv200
  subst v200Value
  let zhAcc1 : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 ((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5)))), .value (BitVec.ofNat 64 ((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0)), .value (BitVec.ofNat 64 (0 + 0)), .value (BitVec.ofNat 64 (0 + 0)), .value (BitVec.ofNat 64 (0 + 0)), .value (BitVec.ofNat 64 (0 + 0)), .poison, .poison]
  have v201Value : v201 = zhAcc1 := by denote_vecbin hv201
  subst v201Value
  let zhAcc2 : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 (((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) + (ph (x_4) (y_3) + pl (x_5) (y_3)))), .value (BitVec.ofNat 64 (((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4)))), .value (BitVec.ofNat 64 ((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5)))), .value (BitVec.ofNat 64 ((0 + 0) + 0)), .value (BitVec.ofNat 64 ((0 + 0) + 0)), .value (BitVec.ofNat 64 ((0 + 0) + 0)), .poison, .poison]
  have v202Value : v202 = zhAcc2 := by denote_vecbin hv202
  subst v202Value
  let zh : Vector (PoisonOr (BitVec 64)) 8 := #v[.value (BitVec.ofNat 64 ((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) + (ph (x_4) (y_3) + pl (x_5) (y_3))) + ph (x_5) (y_2))), .value (BitVec.ofNat 64 ((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) + ph (x_5) (y_3))), .value (BitVec.ofNat 64 (((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4))), .value (BitVec.ofNat 64 (((0 + 0) + 0) + ph (x_5) (y_5))), .value (BitVec.ofNat 64 (((0 + 0) + 0) + 0)), .value (BitVec.ofNat 64 (((0 + 0) + 0) + 0)), .poison, .poison]
  have v203Value : v203 = zh := by denote_vecbin hv203
  subst v203Value
  denote_clear v 195 203

  -- `%204` = `za`, `%205` = `zb`, `%206`-`%209`: the final fold.
  denote_step_all v 209
  let za := toBitVecValue 64 #v[(((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0) + 0, ((((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0) + 0, ((((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0))) + 0) + 0) + 0) + 0, ((((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1))) + (ph (x_2) (y_0) + pl (x_3) (y_0))) + 0) + 0) + 0, ((((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2))) + (ph (x_2) (y_1) + pl (x_3) (y_1))) + (ph (x_3) (y_0) + pl (x_4) (y_0))) + 0) + 0, ((((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3))) + (ph (x_2) (y_2) + pl (x_3) (y_2))) + (ph (x_3) (y_1) + pl (x_4) (y_1))) + (ph (x_4) (y_0) + pl (x_5) (y_0))) + 0, 0, 0]
  have v204Value : v204 = za := by denote_vecbin hv204
  subst v204Value
  let zb := toBitVecValue 64 #v[((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3))) + (ph (x_3) (y_2) + pl (x_4) (y_2))) + (ph (x_4) (y_1) + pl (x_5) (y_1))) + ph (x_5) (y_0), (((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) + (ph (x_3) (y_3) + pl (x_4) (y_3))) + (ph (x_4) (y_2) + pl (x_5) (y_2))) + ph (x_5) (y_1), (((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) + (ph (x_4) (y_3) + pl (x_5) (y_3))) + ph (x_5) (y_2), (((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) + ph (x_5) (y_3), ((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4), ((0 + 0) + 0) + ph (x_5) (y_5), ((0 + 0) + 0) + 0, ((0 + 0) + 0) + 0]
  have v205Value : v205 = zb := by mul_shuffle hv205
  subst v205Value
  let zbShl7 := toBitVecValue 64 #v[(((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3))) + (ph (x_3) (y_2) + pl (x_4) (y_2))) + (ph (x_4) (y_1) + pl (x_5) (y_1))) + ph (x_5) (y_0)) * 128, ((((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) + (ph (x_3) (y_3) + pl (x_4) (y_3))) + (ph (x_4) (y_2) + pl (x_5) (y_2))) + ph (x_5) (y_1)) * 128, ((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) + (ph (x_4) (y_3) + pl (x_5) (y_3))) + ph (x_5) (y_2)) * 128, ((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) + ph (x_5) (y_3)) * 128, (((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4)) * 128, (((0 + 0) + 0) + ph (x_5) (y_5)) * 128, (((0 + 0) + 0) + 0) * 128, (((0 + 0) + 0) + 0) * 128]
  have v206Value : v206 = zbShl7 := by denote_vecbin hv206
  subst v206Value
  let zbShl7Za := toBitVecValue 64 #v[((((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3))) + (ph (x_3) (y_2) + pl (x_4) (y_2))) + (ph (x_4) (y_1) + pl (x_5) (y_1))) + ph (x_5) (y_0)) * 128) + ((((((0 + pl (x_0) (y_0)) + 0) + 0) + 0) + 0) + 0), (((((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) + (ph (x_3) (y_3) + pl (x_4) (y_3))) + (ph (x_4) (y_2) + pl (x_5) (y_2))) + ph (x_5) (y_1)) * 128) + (((((((ph (x_0) (y_0) + pl (x_1) (y_0)) + pl (x_0) (y_1)) + 0) + 0) + 0) + 0) + 0), (((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) + (ph (x_4) (y_3) + pl (x_5) (y_3))) + ph (x_5) (y_2)) * 128) + (((((((ph (x_0) (y_1) + pl (x_1) (y_1)) + pl (x_0) (y_2)) + (ph (x_1) (y_0) + pl (x_2) (y_0))) + 0) + 0) + 0) + 0), (((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) + ph (x_5) (y_3)) * 128) + (((((((ph (x_0) (y_2) + pl (x_1) (y_2)) + pl (x_0) (y_3)) + (ph (x_1) (y_1) + pl (x_2) (y_1))) + (ph (x_2) (y_0) + pl (x_3) (y_0))) + 0) + 0) + 0), ((((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4)) * 128) + (((((((ph (x_0) (y_3) + pl (x_1) (y_3)) + pl (x_0) (y_4)) + (ph (x_1) (y_2) + pl (x_2) (y_2))) + (ph (x_2) (y_1) + pl (x_3) (y_1))) + (ph (x_3) (y_0) + pl (x_4) (y_0))) + 0) + 0), ((((0 + 0) + 0) + ph (x_5) (y_5)) * 128) + (((((((ph (x_0) (y_4) + pl (x_1) (y_4)) + pl (x_0) (y_5)) + (ph (x_1) (y_3) + pl (x_2) (y_3))) + (ph (x_2) (y_2) + pl (x_3) (y_2))) + (ph (x_3) (y_1) + pl (x_4) (y_1))) + (ph (x_4) (y_0) + pl (x_5) (y_0))) + 0), ((((0 + 0) + 0) + 0) * 128) + (0), ((((0 + 0) + 0) + 0) * 128) + (0)]
  have v207Value : v207 = zbShl7Za := by denote_vecbin hv207
  let zbMul24 := toBitVecValue 64 #v[(((((((ph (x_0) (y_5) + pl (x_1) (y_5)) + 0) + (ph (x_1) (y_4) + pl (x_2) (y_4))) + (ph (x_2) (y_3) + pl (x_3) (y_3))) + (ph (x_3) (y_2) + pl (x_4) (y_2))) + (ph (x_4) (y_1) + pl (x_5) (y_1))) + ph (x_5) (y_0)) * 24, ((((((0 + 0) + (ph (x_1) (y_5) + pl (x_2) (y_5))) + (ph (x_2) (y_4) + pl (x_3) (y_4))) + (ph (x_3) (y_3) + pl (x_4) (y_3))) + (ph (x_4) (y_2) + pl (x_5) (y_2))) + ph (x_5) (y_1)) * 24, ((((ph (x_3) (y_4) + pl (x_4) (y_4)) + (ph (x_2) (y_5) + pl (x_3) (y_5))) + (ph (x_4) (y_3) + pl (x_5) (y_3))) + ph (x_5) (y_2)) * 24, ((((ph (x_3) (y_5) + pl (x_4) (y_5)) + 0) + (ph (x_4) (y_4) + pl (x_5) (y_4))) + ph (x_5) (y_3)) * 24, (((0 + 0) + (ph (x_4) (y_5) + pl (x_5) (y_5))) + ph (x_5) (y_4)) * 24, (((0 + 0) + 0) + ph (x_5) (y_5)) * 24, (((0 + 0) + 0) + 0) * 24, (((0 + 0) + 0) + 0) * 24]
  have v208Value : v208 = zbMul24 := by denote_vecbin hv208
  subst v207Value v208Value
  -- `%209`: the final add, against the specified limbs directly. The lane
  -- sums are already N-level, so only `limb`/`col` unfolding and `ring`
  -- remain (`152 = 128 + 24` is where the two fold terms meet).
  have v209Value : v209 = (mulVec x y).map PoisonOr.value := by
    simp only [mulVec, limbVec]
    denote_vecbin hv209
    all_goals try congr 1
    all_goals try simp [limb, col, limbNat, ph, pl]
    all_goals try ring_nf
  subst v209Value
  simp_peephole

abbrev mulValue (x y : Vector (BitVec 64) 8) := (fd_r43x6_mul_fast.denote
          (Ctxt.Valuation.ofPair (y.map PoisonOr.value) (x.map PoisonOr.value))).head.getValues

abbrev mulIsMul (x y : Vector (BitVec 64) 8) :=
    (fun l => (R43x6.decode' l : ZMod p)) <$> mulValue x y
      = .value ((R43x6.decode' x : ZMod p) * (R43x6.decode' y : ZMod p))

private def output_bounds_u44_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U44 x → R43x6.U44 y → R43x6.U62 (mulValue x y).getValue
private def output_bounds_u45_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U45 x → R43x6.U45 y → R43x6.U62 (mulValue x y).getValue
private def output_bounds_u46_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U46 x → R43x6.U46 y → R43x6.U62 (mulValue x y).getValue
private def output_bounds_u47_u63 (x y : Vector (BitVec 64) 8) :=
  R43x6.U47 x → R43x6.U47 y → R43x6.U63 (mulValue x y).getValue

set_option maxHeartbeats 1000000 in
private theorem mulIsMulThm (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulIsMul x y := by
  have hbx : ∀ i : Fin 6, limbNat x i < 2^47 := limbNat_lt x 47 (by omega) hx
  have hby : ∀ i : Fin 6, limbNat y i < 2^47 := limbNat_lt y 47 (by omega) hy
  -- 1. denotation to lanes to specified limbs; the poison layer collapses
  rw [mulIsMul, mulValue, denote_fd_r43x6_mul_fast x y hx hy hy6 hy7]
  simp only [HVector.head, Vector.getValues_map_value, PoisonOr.map_value,
    PoisonOr.value_inj]
  -- 2. decode both sides into casts of `decodeNat`
  have hdecode : ∀ (v : Vector (BitVec 64) 8), R43x6.Unreduced v →
      R43x6.decode' v = ((decodeNat (limbNat v) : ℕ) : Int) := by
    intro v hv
    have hv8 : v = #v[v[0],v[1],v[2],v[3],v[4],v[5],v[6],v[7]] := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    have hb : ∀ i : Fin 6, limbNat v i < 2^47 := limbNat_lt v 47 (by omega) hv
    conv_lhs => rw [hv8]
    rw [decode'_lit,
      toInt_of_lt (by simpa [limbNat] using hb 0),
      toInt_of_lt (by simpa [limbNat] using hb 1),
      toInt_of_lt (by simpa [limbNat] using hb 2),
      toInt_of_lt (by simpa [limbNat] using hb 3),
      toInt_of_lt (by simpa [limbNat] using hb 4),
      toInt_of_lt (by simpa [limbNat] using hb 5)]
    push_cast [decodeNat_eq, limbNat]
    try ring
  rw [mulVec, decode'_limbVec _ (limb_lt_two_pow_63 _ _ hbx hby),
    hdecode x hx, hdecode y hy]
  -- 3. both sides are now casts of `decodeNat`, so `decodeLimbs_limb_zmod` applies
  push_cast
  exact decodeLimbs_limb_zmod (limbNat x) (limbNat y)

/-! ## Output bounds

The four rows of the `fd_r43x6.h` table, each `limb_lt_u4x` transported
through the denotation: output lane `k < 6` is the specified limb, lanes 6
and 7 are zero, and none is read back as negative. -/

/-- The program's result, with the poison layer discharged. -/
private theorem mulValue_eq (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulValue x y = .value (mulVec x y) := by
  rw [mulValue, denote_fd_r43x6_mul_fast x y hx hy hy6 hy7]
  simp only [HVector.head, Vector.getValues_map_value]

/-- Two-sided lane bounds from a ceiling `N` on the ℕ-level limbs. -/
private theorem output_bounds_of (x y : Vector (BitVec 64) 8) (N : ℕ) (hN : N ≤ 2^63)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0)
    (hb : ∀ k, limb (limbNat x) (limbNat y) k < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (mulValue x y).getValue
      ∧ R43x6.BoundedLower 0 (mulValue x y).getValue := by
  have hv : (mulValue x y).getValue = mulVec x y := by
    rw [mulValue_eq x y hx hy hy6 hy7]; rfl
  rw [hv, mulVec]
  exact limbVec_bounds _ N hN hb

private theorem output_u44 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u44_u62 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2^62 := fun k =>
    limb_lt_u44 _ _ (limbNat_lt x 44 (by omega) hinx) (limbNat_lt y 44 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u45 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u45_u62 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2^62 := fun k =>
    limb_lt_u45 _ _ (limbNat_lt x 45 (by omega) hinx) (limbNat_lt y 45 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u46 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u46_u62 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2^62 := fun k =>
    limb_lt_u46 _ _ (limbNat_lt x 46 (by omega) hinx) (limbNat_lt y 46 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u47 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u47_u63 x y := by
  intro hinx hiny
  have hb : ∀ k, limb (limbNat x) (limbNat y) k < 2^63 := fun k =>
    limb_lt_u47 _ _ (limbNat_lt x 47 (by omega) hinx) (limbNat_lt y 47 (by omega) hiny) k
  exact_mod_cast output_bounds_of x y (2^63) (by omega) hx hy hy6 hy7 hb

/-- **Specification of `fd_r43x6_mul_fast`**: on unreduced inputs whose `y`
high lanes are zero, the six output limbs decode to the product of the decoded
inputs in `GF(2^255 - 19)`, and the four input/output width guarantees of
`fd_r43x6.h` hold. -/
theorem spec_fd_r43x6_mul_fast (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulIsMul x y ∧ output_bounds_u44_u62 x y ∧ output_bounds_u45_u62 x y
      ∧ output_bounds_u46_u62 x y ∧ output_bounds_u47_u63 x y :=
  ⟨mulIsMulThm x y hx hy hy6 hy7, output_u44 x y hx hy hy6 hy7,
    output_u45 x y hx hy hy6 hy7, output_u46 x y hx hy hy6 hy7,
    output_u47 x y hx hy hy6 hy7⟩

end Firedancer.Avx512

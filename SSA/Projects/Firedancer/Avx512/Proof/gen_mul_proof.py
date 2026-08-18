#!/usr/bin/env python3
"""Generate SSA/Projects/Firedancer/Avx512/Proof/fd_r43x6_mul_fast.lean.

Mirrors the data flow of fd_r43x6_mul_fast.mlir (instruction indices %0-%209)
and the structure of the sqr_fast proof. Every intermediate is stated at the
N level, over the `pl`/`ph` limb functions of Spec/Common.lean.

Usage: gen_mul_proof.py [--upto N]  (truncate proof after instruction N, close with sorry)
"""
import sys

UPTO = None
if len(sys.argv) >= 3 and sys.argv[1] == '--upto':
    UPTO = int(sys.argv[2])

# ---------------------------------------------------------------- lane algebra

# Lanes 6 and 7 of `y` are zero by the contract, so every product against them
# is zero and is emitted as such: `pl a 0 = ph a 0 = 0`. That is what keeps the
# derivation from ever forming a term the specification does not have.
def zeroY(j):
    return j >= 6

def T(i, j):
    """t_i lane j, as a Lean expression string (uncertain outer parens)."""
    if zeroY(j):
        return "0"
    if i == 0:
        return f"pl (x_0) (y_{j})"
    if i == 6:
        return f"ph (x_5) (y_{j})"
    return f"ph (x_{i-1}) (y_{j}) + pl (x_{i}) (y_{j})"

def Tp(i, j):
    """t_i lane j, parenthesized if compound (a top-level `+`)."""
    t = T(i, j)
    return f"({t})" if i in range(1, 6) and not zeroY(j) else t

def hi(i, j):
    """the raw `vpmadd52h` lane, before the `<<< 9` that scales it into `ph`."""
    return "0" if zeroY(j) else f"phRaw (x_{i}) (y_{j})"

def hs(i, j):
    return "0" if zeroY(j) else f"ph (x_{i}) (y_{j})"

# p_i j  (i = 1..6): slide(zero, t_i, 8-i); lane j = t_i[j-i], 0 for j < i
def p_lane(i, j):
    return Tp(i, j - i) if j >= i else "0"

# q_i m  (i = 3..6): slide(t_i, zero, 8-i); lane m = t_i[m+8-i] for m <= i-1,
# 0 for i <= m <= 5, poison for m = 6, 7 (encoded None)
def q_lane(i, m):
    if m >= 6:
        return None
    if m <= i - 1:
        return Tp(i, m + 8 - i)
    return "0"

# zl accumulation: v195 = p1+t0, v196 += p2, v197 += p3, v198 += p4, v199 += p5, v200 += p6
zl_steps = []          # zl_steps[s][j] = lane expr after step s (s = 0..5)
acc = [f"{p_lane(1, j)} + {Tp(0, j)}" for j in range(8)]
zl_steps.append(list(acc))
for i in (2, 3, 4, 5, 6):
    acc = [f"({acc[j]}) + {p_lane(i, j)}" for j in range(8)]
    zl_steps.append(list(acc))
zl = zl_steps[-1]

# zh accumulation: v201 = q4+q3, v202 += q5, v203 += q6  (lanes 6,7 poison)
zh_steps = []
acc = []
for m in range(8):
    a, b = q_lane(4, m), q_lane(3, m)
    acc.append(None if a is None else f"{a} + {b}")
zh_steps.append(list(acc))
for i in (5, 6):
    nxt = []
    for m in range(8):
        q = q_lane(i, m)
        nxt.append(None if acc[m] is None else f"({acc[m]}) + {q}")
    acc = nxt
    zh_steps.append(list(acc))
zh = zh_steps[-1]

za = [zl[j] for j in range(6)] + ["0", "0"]
zb = [zl[6], zl[7]] + [zh[m] for m in range(6)]

zb_shl7   = [f"({zb[j]}) * 128" for j in range(8)]
zb_shl7za = [f"(({zb[j]}) * 128) + ({za[j]})" for j in range(8)]
zb_mul24  = [f"({zb[j]}) * 24" for j in range(8)]

# ---------------------------------------------------------------- emit helpers

out = []
def emit(s=""):
    out.append(s)

def vec_values(name, lanes, comment=None):
    """let <name> := toBitVecValue 64 #v[...]  (all-value lanes, N-level)"""
    if comment:
        emit(f"  -- {comment}")
    body = ", ".join(lanes)
    emit(f"  let {name} := toBitVecValue 64 #v[{body}]")

def vec_mixed(name, lanes, comment=None):
    """let <name> : Vector (PoisonOr (BitVec 64)) 8 := #v[...]  (None = poison)"""
    if comment:
        emit(f"  -- {comment}")
    parts = [".poison" if l is None else f".value (BitVec.ofNat 64 ({l}))"
             for l in lanes]
    body = ", ".join(parts)
    emit(f"  let {name} : Vector (PoisonOr (BitVec 64)) 8 := #v[{body}]")

def have_tac(v, name, tac):
    emit(f"  have v{v}Value : v{v} = {name} := by {tac} hv{v}")

def subst(*vs):
    emit("  subst " + " ".join(f"v{v}Value" for v in vs))

STOPPED = False
def stop_check(n):
    """If truncating, emit sorry and cut off."""
    global STOPPED
    if UPTO is not None and n > UPTO and not STOPPED:
        emit("  sorry")
        STOPPED = True
    return STOPPED

MOVED_TAIL = r"""abbrev mulValue (x y : Vector (BitVec 64) 8) := (fd_r43x6_mul_fast.denote
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

/-- The limbs of an unreduced input, bounded as naturals. -/
private theorem limbNat_lt (x : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x) :
    ∀ i < 6, limbNat x i < 2^47 := by
  intro i hi
  interval_cases i <;>
    simpa [limbNat] using unn_toNat x 47 (by omega) hx _ (by omega)

set_option maxHeartbeats 1000000 in
private theorem mulIsMulThm (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulIsMul x y := by
  have hbx : ∀ i < 6, limbNat x i < 2^47 := limbNat_lt x hx
  have hby : ∀ i < 6, limbNat y i < 2^47 := limbNat_lt y hy
  -- 1. denotation to lanes to specified limbs; the poison layer collapses
  rw [mulIsMul, mulValue, denote_fd_r43x6_mul_fast x y hx hy hy6 hy7]
  simp only [HVector.head, Vector.getValues_map_value, PoisonOr.map_value,
    PoisonOr.value_inj]
  -- 2. decode both sides into casts of `pack`
  have hdecode : ∀ (v : Vector (BitVec 64) 8), R43x6.Unreduced v →
      R43x6.decode' v = ((pack (limbNat v) : ℕ) : Int) := by
    intro v hv
    have hv8 : v = #v[v[0],v[1],v[2],v[3],v[4],v[5],v[6],v[7]] := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    have hb : ∀ i < 6, limbNat v i < 2^47 := limbNat_lt v hv
    conv_lhs => rw [hv8]
    rw [decode'_lit,
      toInt_of_lt (by simpa [limbNat] using hb 0 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 1 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 2 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 3 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 4 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 5 (by omega))]
    push_cast [pack, limbNat]
    try ring
  rw [mulVec, decode'_limbVec _ (limb_lt_two_pow_63 _ _ hbx hby),
    hdecode x hx, hdecode y hy]
  -- 3. both sides are now casts of `pack`, so `pack_limb_zmod` applies
  push_cast
  exact pack_limb_zmod (limbNat x) (limbNat y)

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
    (hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < N) :
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
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^62 := fun k hk =>
    limb_lt_u44 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 44 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 44 (by omega) hiny _ (by omega))
      k hk
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u45 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u45_u62 x y := by
  intro hinx hiny
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^62 := fun k hk =>
    limb_lt_u45 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 45 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 45 (by omega) hiny _ (by omega))
      k hk
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u46 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u46_u62 x y := by
  intro hinx hiny
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^62 := fun k hk =>
    limb_lt_u46 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 46 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 46 (by omega) hiny _ (by omega))
      k hk
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u47 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u47_u63 x y := by
  intro hinx hiny
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^63 := fun k hk =>
    limb_lt_u47 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 47 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 47 (by omega) hiny _ (by omega))
      k hk
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
"""

# ---------------------------------------------------------------- file header

emit("""/-
Released under Apache 2.0 license as described in the file LICENSE.
NOTE: the bulk of this file is generated by a script
(`gen_mul_proof.py`); the structure mirrors the data flow of
`fd_r43x6_mul_fast`.
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
""")

# ------------------------------------------------------- main theorem

emit("set_option maxHeartbeats 400000000 in")
emit("set_option maxRecDepth 1000000 in")
emit("/-- **Limb derivation** for `fd_r43x6_mul_fast`: on unreduced inputs whose")
emit("two high `y` lanes are zero, the denotation *is* the specified limb vector")
emit("`mulVec x y` -- every one of the 209 instructions carried through at the N")
emit("level. -/")
emit("theorem denote_fd_r43x6_mul_fast (x y : Vector (BitVec 64) 8)")
emit("    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)")
emit("    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :")
emit("    fd_r43x6_mul_fast.denote")
emit("        (Ctxt.Valuation.ofPair (y.map PoisonOr.value) (x.map PoisonOr.value)) =")
emit("      ([(mulVec x y).map PoisonOr.value]ₕ :")
emit("        HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))]) := by")
emit("  -- The operand bounds that make each `vpmadd52` truncation the identity.")
# Stated on `.toNat`, the form the lane goals are in once `limbNat` unfolds.
for v, n in (("x", 6), ("y", 6)):
    for i in range(n):
        emit(f"  have b{v}{i} : {v}[{i}].toNat < 2^47 :=")
        emit(f"    unn_toNat {v} 47 (by omega) h{v} {i} (by omega)")
for v, n in (("x", 6), ("y", 6)):
    for i in range(n):
        emit(f"  have t{v}{i} : {v}[{i}].toNat < 4503599627370496 := by omega")
emit("  unfold fd_r43x6_mul_fast")

# constants %0-%4
emit("  denote_step_all v 4")
emit("  let zeroBVP : PoisonOr (BitVec 64) := .value 0")
emit("  let neg1BVP : PoisonOr (BitVec 64) := .value (-1)")
emit("  let zeroVec := toBitVecValue 64 (Vector.replicate 8 0)")
emit("  let nineVec := toBitVecValue 64 (Vector.replicate 8 9)")
emit("  have v1Zero : v1 = zeroBVP := by")
emit("    simp only [hv1, Expr.denoteOp1, Expr.denoteOpPure]")
emit("    simp_peephole")
emit("    simp only [HVector.head]")
emit("    rfl")
emit("  have v2Value : v2 = zeroVec := by denote_dense hv2")
emit("  have v3Value : v3 = nineVec := by denote_dense hv3")
emit("  have v4Poison : v4 = PoisonOr.poison := by")
emit("    simp only [hv4]")
emit("    simp_peephole")
emit("    rfl")
emit("  subst v1Zero v2Value v3Value v4Poison")
emit("  clear hv0 hv1 hv2 hv3 hv4")
emit()

if not stop_check(5):
    # the nine wwl_slide zero operands, insertelement chains
    chains = [
        # (end, name, n_first, first_kind) -- first_kind 'p' = poison-first
        (21,  "p7z1", 7, 'p'),
        (38,  "p6z2", 6, 'p'),
        (55,  "p5z3", 5, 'p'),
        (72,  "z3p5", 3, 'z'),
        (89,  "p4z4", 4, 'p'),
        (106, "z2p6", 2, 'z'),
        (123, "p3z5", 3, 'p'),
        (140, "z1p7", 1, 'z'),
        (157, "p2z6", 2, 'p'),
    ]
    emit("  -- The `wwl_slide` zero operands: an `undef` vector with zero written into")
    emit("  -- the lanes each slide actually reads, the rest left poison.")
    start = 5
    for (end, name, n, kind) in chains:
        if stop_check(start):
            break
        if kind == 'p':
            first = f"(Vector.replicate {n} (PoisonOr.poison : PoisonOr (BitVec 64)))"
            second = f"(Vector.replicate {8-n} (.value (BitVec.zero 64)))"
        else:
            first = f"(Vector.replicate {n} (PoisonOr.value (BitVec.zero 64)))"
            second = f"(Vector.replicate {8-n} (.poison : PoisonOr (BitVec 64)))"
        emit(f"  let {name} : Vector (PoisonOr (BitVec 64)) 8 := {first}.append {second}")
        emit(f"  denote_step_all v {end}")
        emit(f"  have v{end}Value : v{end} = {name} := by")
        emit(f"    denote_eval v {start} {end}")
        emit(f"    denote_expand v {start} {end}")
        emit(f"    simp [LLVM.Ty.insertelement, LLVM.Ty.poison, LLVM.const?]")
        emit(f"    rfl")
        emit(f"  subst v{end}Value")
        emit(f"  denote_clear v {start} {end}")
        emit()
        start = end + 1

if not stop_check(158):
    emit("  -- `%158`-`%160`: the `za` mask and the fold constants.")
    emit("  let zaMask : Vector (PoisonOr (BitVec 64)) 8 :=")
    emit("    #v[neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, neg1BVP, zeroBVP, zeroBVP]")
    emit("  let dense7 := toBitVecValue 64 (Vector.replicate 8 7)")
    emit("  let dense24 := toBitVecValue 64 (Vector.replicate 8 24)")
    emit("  denote_step_all v 160")
    have_tac(158, "zaMask", "denote_dense")
    have_tac(159, "dense7", "denote_dense")
    have_tac(160, "dense24", "denote_dense")
    subst(158, 159, 160)
    emit("  denote_clear v 158 160")
    emit()

if not stop_check(161):
    emit("  -- Name the lanes once, so the uses below do not each re-elaborate an")
    emit("  -- `x[i]`/`y[j]` bounds proof.")
    for i in range(6):
        emit(f"  let x_{i} : ℕ := limbNat x {i}")
    for j in range(6):
        emit(f"  let y_{j} : ℕ := limbNat y {j}")
    emit()
    emit("  -- `%161`-`%166` = `x0`-`x5`: `wwl_permute( wwl_bcast( iL ), x )`.")
    emit("  denote_step_all v 166")
    for i in range(6):
        vec_values(f"xb{i}", [f"x_{i}"] * 8)
    for i in range(6):
        have_tac(161 + i, f"xb{i}", "mul_shuffle")
    subst(*range(161, 167))
    emit("  denote_clear v 161 166")
    emit()

if not stop_check(167):
    emit("  -- `%167`-`%184` = `t0`-`t6`: `t_i = wwl_madd52lo( wwl_shl( wwl_madd52hi( zero, x_(i-1), y ), 9 ), x_i, y )`.")
    emit("  denote_step_all v 184")
    # t0
    vec_values("t0", [T(0, j) for j in range(8)])
    have_tac(167, "t0", "mul_vpmadd52")
    subst(167)
    v = 168
    for i in range(6):
        if stop_check(v):
            break
        vec_values(f"hi{i}", [hi(i, j) for j in range(8)])
        have_tac(v, f"hi{i}", "mul_vpmadd52")
        subst(v)
        v += 1
        shifted = [hs(i, j) for j in range(8)]
        if i < 5:
            vec_values(f"hs{i}", shifted)
            have_tac(v, f"hs{i}", "denote_vecbin")
            subst(v)
            v += 1
            vec_values(f"t{i+1}", [T(i + 1, j) for j in range(8)])
            have_tac(v, f"t{i+1}", "mul_vpmadd52")
            subst(v)
            v += 1
        else:
            vec_values("t6", shifted)
            have_tac(v, "t6", "denote_vecbin")
            subst(v)
            v += 1
    if not STOPPED:
        emit("  denote_clear v 167 184")
        emit()

if not stop_check(185):
    emit("  -- `%185`-`%194`: the `wwl_slide` shuffles `p1j`-`p6j` and `q3j`-`q6j`.")
    emit("  denote_step_all v 194")
    slide_v = {185: ("p1j", 1, 'p'), 186: ("p2j", 2, 'p'), 187: ("p3j", 3, 'p'),
               188: ("q3j", 3, 'q'), 189: ("p4j", 4, 'p'), 190: ("q4j", 4, 'q'),
               191: ("p5j", 5, 'p'), 192: ("q5j", 5, 'q'), 193: ("p6j", 6, 'p'),
               194: ("q6j", 6, 'q')}
    for v in range(185, 195):
        name, i, kind = slide_v[v]
        if kind == 'p':
            vec_values(name, [p_lane(i, j) for j in range(8)])
        else:
            vec_mixed(name, [q_lane(i, m) for m in range(8)])
        have_tac(v, name, "mul_shuffle")
        subst(v)
    emit("  denote_clear v 185 194")
    emit()

if not stop_check(195):
    emit("  -- `%195`-`%200` = `zl`, `%201`-`%203` = `zh`: the big adds.")
    emit("  denote_step_all v 203")
    add_names = ["zlAcc1", "zlAcc2", "zlAcc3", "zlAcc4", "zlAcc5", "zl"]
    for s, name in enumerate(add_names):
        vec_values(name, zl_steps[s])
        have_tac(195 + s, name, "denote_vecbin")
        subst(195 + s)
    zh_names = ["zhAcc1", "zhAcc2", "zh"]
    for s, name in enumerate(zh_names):
        vec_mixed(name, zh_steps[s])
        have_tac(201 + s, name, "denote_vecbin")
        subst(201 + s)
    emit("  denote_clear v 195 203")
    emit()

if not stop_check(204):
    emit("  -- `%204` = `za`, `%205` = `zb`, `%206`-`%209`: the final fold.")
    emit("  denote_step_all v 209")
    vec_values("za", za)
    have_tac(204, "za", "denote_vecbin")
    subst(204)
    vec_values("zb", zb)
    have_tac(205, "zb", "mul_shuffle")
    subst(205)
    vec_values("zbShl7", zb_shl7)
    have_tac(206, "zbShl7", "denote_vecbin")
    subst(206)
    vec_values("zbShl7Za", zb_shl7za)
    have_tac(207, "zbShl7Za", "denote_vecbin")
    vec_values("zbMul24", zb_mul24)
    have_tac(208, "zbMul24", "denote_vecbin")
    subst(207, 208)
    emit("  -- `%209`: the final add, against the specified limbs directly. The lane")
    emit("  -- sums are already N-level, so only `limb`/`col` unfolding and `ring`")
    emit("  -- remain (`152 = 128 + 24` is where the two fold terms meet).")
    emit("  have v209Value : v209 = (mulVec x y).map PoisonOr.value := by")
    emit("    simp only [mulVec, limbVec]")
    emit("    denote_vecbin hv209")
    emit("    all_goals try congr 1")
    emit("    all_goals try simp only [limb, col, limbNat, ph, pl]")
    emit("    all_goals try ring_nf")
    emit("  subst v209Value")
    emit("  simp_peephole")

emit()
if not STOPPED:
    # The `ZMod p` statement and the four width rows of the `fd_r43x6.h` table,
    # unchanged from the split layout except that each now reaches the
    # denotation in a single rewrite.
    emit(MOVED_TAIL)
emit("end Firedancer.Avx512")

import os
path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fd_r43x6_mul_fast.lean")
with open(path, "w") as f:
    f.write("\n".join(out) + "\n")
print(f"wrote {path} ({len(out)} lines, upto={UPTO})")

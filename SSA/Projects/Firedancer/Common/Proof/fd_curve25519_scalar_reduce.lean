/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Common.Proof.fd_ulong_load_8
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_curve25519_scalar_reduce` conforms -- the load section

Work in progress. What is derived here is the region's prefix: the fifty-one
constants and the eight `fd_ulong_load_8` calls that read `in` at 0, 8, ..., 56,
leaving the eight loaded words named and the walk positioned at `%66`, the
first instruction of the unpacking.

The eight loads are the only reason the region can run in place. They all
precede the first store, so each reads the *entry* state's `in`: `word i` below
is `readWord` at `in + 8i` in `s`, transported forward through the calls'
equivalences rather than re-read at the state each call leaves.

`%66`-`%111` is the unpacking, and it is done: twenty-four digits, each named
with the bound it carries. That block is pure `and`/`lshr`/`fshl` with not one
overflow flag, so nothing in it can go poison and no side condition arises --
the first flagged instruction is `%112`.

What remains is the reduction proper and the four stores. That part is where
the cost is: 224 of the region's operations carry `nsw`, 42 of them `nuw` as
well, and each is poison unless the corresponding bound is discharged. The
digits' bounds here are where those discharges start. Note that the C works in
`long` and several digits go negative once the reduction begins subtracting, so
the bounds needed there are two-sided on `toInt`, not one-sided on `toNat`.

The callee is taken in *continuation* form (`fd_ulong_load_8_conforms_cont`)
rather than destructed with `obtain`. `obtain` is `cases`, which reverts the
goal and reintroduces it once per layer, and the goal here carries the whole
residual region -- 498 instructions at the first call, still over 430 at the
eighth. Three layers times eight calls is the difference between a file that
elaborates in seconds and one that does not.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

-- reached only through its conformance theorem
attribute [local irreducible] fd_ulong_load_8

/-! ## Signed overflow

`Proof/Overflow.lean`'s `saddOverflow_eq_false` and `smulOverflow_eq_false`
assume both operands non-negative. That holds for the digits, but not past the
first reduction row: the C works in `long` and `s14 -= s23*997805L` drives
operands negative, with `-997805` reaching the region as an `i64` constant. The
two-sided forms below are what those rows need.

`saddOverflow`/`smulOverflow` are *defined* on `toInt`, so each is one `omega`
over an atom. -/

/-- Signed addition does not overflow when the exact sum is in range. -/
theorem saddOverflow_eq_false_toInt {u v : BitVec 64}
    (hlo : -(2 ^ 63) ≤ u.toInt + v.toInt) (hhi : u.toInt + v.toInt < 2 ^ 63) :
    u.saddOverflow v = false := by
  simp only [BitVec.saddOverflow, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt]
  omega

/-- ... and likewise for multiplication. -/
theorem smulOverflow_eq_false_toInt {u v : BitVec 64}
    (hlo : -(2 ^ 63) ≤ u.toInt * v.toInt) (hhi : u.toInt * v.toInt < 2 ^ 63) :
    u.smulOverflow v = false := by
  simp only [BitVec.smulOverflow, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt]
  omega

/-! ## Flagged registers that carry a value

One lemma per flag combination the region actually uses. Discharging the guards
is what turns a flagged operation from a `do` block into a plain value, which is
what the stepper needs to keep going. -/

theorem mul_nsw {x y : BitVec 64} (h : x.smulOverflow y = false) :
    LLVM.mul (PoisonOr.value x) (PoisonOr.value y) {nsw := true, nuw := false}
      = PoisonOr.value (x * y) := by
  simp [LLVM.mul, LLVM.mul?, h]

theorem mul_nsw_nuw {x y : BitVec 64} (hs : x.smulOverflow y = false)
    (hu : x.umulOverflow y = false) :
    LLVM.mul (PoisonOr.value x) (PoisonOr.value y) {nsw := true, nuw := true}
      = PoisonOr.value (x * y) := by
  simp [LLVM.mul, LLVM.mul?, hs, hu]

theorem add_nsw {x y : BitVec 64} (h : x.saddOverflow y = false) :
    LLVM.add (PoisonOr.value x) (PoisonOr.value y) {nsw := true, nuw := false}
      = PoisonOr.value (x + y) := by
  simp [LLVM.add, LLVM.add?, h]

theorem add_nsw_nuw {x y : BitVec 64} (hs : x.saddOverflow y = false)
    (hu : x.uaddOverflow y = false) :
    LLVM.add (PoisonOr.value x) (PoisonOr.value y) {nsw := true, nuw := true}
      = PoisonOr.value (x + y) := by
  simp [LLVM.add, LLVM.add?, hs, hu]

/-- Name a subterm without reverting the goal, as `obtain` would. -/
private theorem name_of {α : Sort u} (a : α) {P : Prop} (k : ∀ x, x = a → P) : P := k a rfl

/-- Replace a digit's defining expression by an opaque value carrying its
sign-range. Continuation form, so the walk goal is never reverted.

Abstracting is what keeps the reduction's terms small: after this the digits are
variables, and the `readWord`s they were built from appear nowhere in the rows
that follow. -/
private theorem digit_elim {v : LLVM.IntW 64} {e : BitVec 64} {B : Nat} {P : Prop}
    (hv : v = PoisonOr.value e) (hb : e.toNat < B) (hB : B ≤ 2 ^ 63)
    (k : ∀ d : BitVec 64, v = PoisonOr.value d → 0 ≤ d.toInt → d.toInt < (B : Int) → P) : P := by
  refine k e hv ?_ ?_
  · rw [BitVec.toInt_eq_toNat_of_lt (by omega)]; positivity
  · rw [BitVec.toInt_eq_toNat_of_lt (by omega)]; exact_mod_cast hb

/-- `a * c` stays in signed range when `a` is non-negative and below `A`, and
`c` is a constant of magnitude at most `C`, with `A * C ≤ 2^63`.

Stated two-sided in `c` so one lemma covers both signs: four of the six
reduction multipliers are positive and two -- `-997805` and `-683901` -- are
not, and it is exactly those two that the region marks `nsw` without `nuw`. -/
private theorem mul_range {a c A C : Int} (ha0 : 0 ≤ a) (haA : a < A)
    (hc : -C ≤ c) (hcC : c ≤ C) (hC : 0 < C) (hAC : A * C ≤ 2 ^ 63) :
    -(2 ^ 63) ≤ a * c ∧ a * c < 2 ^ 63 := by
  have h1 : a * c ≤ a * C := by nlinarith
  have h2 : a * (-C) ≤ a * c := by nlinarith
  have h3 : a * C < A * C := by nlinarith
  constructor <;> nlinarith

/-! ## Digit bounds

The unpacking's only job, as far as the rest of the derivation is concerned, is
to establish these two. Every `nsw`/`nuw` obligation from `%112` on is an
arithmetic bound on the digits, and these are where those bounds start. -/

/-- A masked digit is the low 21 bits of something, hence below `2^21`. Twenty
three of the twenty four digits have this shape. -/
private theorem toNat_and_mask21_lt (x : BitVec 64) : (x &&& 2097151#64).toNat < 2 ^ 21 := by
  rw [BitVec.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Carry a bound on a register's value across its defining equation, so a
digit's bound is stated on whatever later reads it rather than on the
expression the stepper happened to leave. -/
private theorem bound_of_value {B : Nat} {v : LLVM.IntW 64} {x : BitVec 64}
    (hv : v = PoisonOr.value x) (hx : x.toNat < B) :
    ∀ d, v = PoisonOr.value d → d.toNat < B := by
  intro d hd
  rw [hv, PoisonOr.value_inj] at hd
  exact hd ▸ hx

/-- `s23` is the one digit the C leaves unmasked -- `(long)( in7>>35 )` -- so
its bound comes from the shift alone: 29 bits, the 512-bit input's top end. -/
private theorem toNat_shiftRight35_lt (x : BitVec 64) :
    (x >>> (35#64).toNat).toNat < 2 ^ 29 := by
  have h : x.toNat < 2 ^ 64 := x.isLt
  have e : (35#64).toNat = 35 := by decide
  simp only [BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fd_curve25519_scalar_reduce_conforms (out inp : Pointer) (s : GlobalState)
    (hs : s.WF) (hin : Fits s.mem inp (64 * 8)) (hout : IsScalar256Ptr s.mem out) :
    fd_curve25519_scalar_reduce_spec out inp s hin := by
  simp only [fd_curve25519_scalar_reduce_spec, Cfg.denote]
  refine run_runFunction' _ ?_

  -- `%0`-`%50`: the constants. Only `%0`-`%6` (8, 16, ..., 56) are substituted;
  -- `peel_gep` matches on the literal offset. The rest stay as variables and
  -- are supplied to each step's own `simp` set instead -- substituting all
  -- fifty-one inlines them into every later term and costs more than it saves.
  denote_step_reduce v 50 [LLVM.const?] fold
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6

  -- `%51`: `fd_ulong_load_8( in )`
  have hf₀ : Fits s.mem inp 64 := Fits.mono hin (by omega)
  refine fd_ulong_load_8_conforms_cont inp s hs hf₀ fun t₀ hcall₀ he₀ => ?_
  peel_call hcall₀
  have hwf₀ : t₀.WF := hs.of_equiv he₀
  have hin₀ : Fits t₀.mem inp (64 * 8) := fits_of_live?_eq (he₀.live inp.id).symm hin

  -- `%52`/`%53`: `in + 8`
  peel_gep 8 with inp, hin₀, t₀ as in8
  refine fd_ulong_load_8_conforms_cont in8 t₀ hwf₀ (Fits.mono hin8 (by bv_omega)) fun t₁ hcall₁ he₁ => ?_
  peel_call hcall₁
  have hwf₁ : t₁.WF := hwf₀.of_equiv he₁
  have hin₁ : Fits t₁.mem inp (64 * 8) := fits_of_live?_eq (he₁.live inp.id).symm hin₀

  -- `%54`/`%55`: `in + 16`
  peel_gep 16 with inp, hin₁, t₁ as in16
  refine fd_ulong_load_8_conforms_cont in16 t₁ hwf₁ (Fits.mono hin16 (by bv_omega)) fun t₂ hcall₂ he₂ => ?_
  peel_call hcall₂
  have hwf₂ : t₂.WF := hwf₁.of_equiv he₂
  have hin₂ : Fits t₂.mem inp (64 * 8) := fits_of_live?_eq (he₂.live inp.id).symm hin₁

  -- `%56`/`%57`: `in + 24`
  peel_gep 24 with inp, hin₂, t₂ as in24
  refine fd_ulong_load_8_conforms_cont in24 t₂ hwf₂ (Fits.mono hin24 (by bv_omega)) fun t₃ hcall₃ he₃ => ?_
  peel_call hcall₃
  have hwf₃ : t₃.WF := hwf₂.of_equiv he₃
  have hin₃ : Fits t₃.mem inp (64 * 8) := fits_of_live?_eq (he₃.live inp.id).symm hin₂

  -- `%58`/`%59`: `in + 32`
  peel_gep 32 with inp, hin₃, t₃ as in32
  refine fd_ulong_load_8_conforms_cont in32 t₃ hwf₃ (Fits.mono hin32 (by bv_omega)) fun t₄ hcall₄ he₄ => ?_
  peel_call hcall₄
  have hwf₄ : t₄.WF := hwf₃.of_equiv he₄
  have hin₄ : Fits t₄.mem inp (64 * 8) := fits_of_live?_eq (he₄.live inp.id).symm hin₃

  -- `%60`/`%61`: `in + 40`
  peel_gep 40 with inp, hin₄, t₄ as in40
  refine fd_ulong_load_8_conforms_cont in40 t₄ hwf₄ (Fits.mono hin40 (by bv_omega)) fun t₅ hcall₅ he₅ => ?_
  peel_call hcall₅
  have hwf₅ : t₅.WF := hwf₄.of_equiv he₅
  have hin₅ : Fits t₅.mem inp (64 * 8) := fits_of_live?_eq (he₅.live inp.id).symm hin₄

  -- `%62`/`%63`: `in + 48`
  peel_gep 48 with inp, hin₅, t₅ as in48
  refine fd_ulong_load_8_conforms_cont in48 t₅ hwf₅ (Fits.mono hin48 (by bv_omega)) fun t₆ hcall₆ he₆ => ?_
  peel_call hcall₆
  have hwf₆ : t₆.WF := hwf₅.of_equiv he₆
  have hin₆ : Fits t₆.mem inp (64 * 8) := fits_of_live?_eq (he₆.live inp.id).symm hin₅

  -- `%64`/`%65`: `in + 56`
  peel_gep 56 with inp, hin₆, t₆ as in56
  refine fd_ulong_load_8_conforms_cont in56 t₆ hwf₆ (Fits.mono hin56 (by bv_omega)) fun t₇ hcall₇ he₇ => ?_
  peel_call hcall₇
  have hwf₇ : t₇.WF := hwf₆.of_equiv he₇

  -- the eight loads are done and no store has run, so the state is still `s`
  have heq : s ≈ t₇ :=
    he₀.trans (he₁.trans (he₂.trans (he₃.trans (he₄.trans (he₅.trans (he₆.trans he₇))))))

  -- `%66`-`%111`: the twenty-four digits. Pure throughout -- `and`, `lshr`,
  -- and one `fshl` per digit that straddles a word boundary -- and the first
  -- overflow flag is at `%112`, so nothing here can go poison.
  denote_step_reduce v 111 [LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?,
    hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15, hv16, hv17, hv18, hv19, hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv27, hv28] fold

  -- The twenty-four digits, abstracted: `sᵢ` is the digit the C calls `sᵢ`,
  -- opaque from here on and carrying only `0 ≤ sᵢ.toInt < 2^21` (`2^29` for
  -- `s23`, the one the C leaves unmasked). Those ranges are the whole input to
  -- the reduction's overflow obligations.
  refine digit_elim hv66 (toNat_and_mask21_lt _) (by norm_num) fun s0 hs0 hs0lo hs0hi => ?_
  refine digit_elim hv68 (toNat_and_mask21_lt _) (by norm_num) fun s1 hs1 hs1lo hs1hi => ?_
  refine digit_elim hv70 (toNat_and_mask21_lt _) (by norm_num) fun s2 hs2 hs2lo hs2hi => ?_
  refine digit_elim hv72 (toNat_and_mask21_lt _) (by norm_num) fun s3 hs3 hs3lo hs3hi => ?_
  refine digit_elim hv74 (toNat_and_mask21_lt _) (by norm_num) fun s4 hs4 hs4lo hs4hi => ?_
  refine digit_elim hv76 (toNat_and_mask21_lt _) (by norm_num) fun s5 hs5 hs5lo hs5hi => ?_
  refine digit_elim hv78 (toNat_and_mask21_lt _) (by norm_num) fun s6 hs6 hs6lo hs6hi => ?_
  refine digit_elim hv80 (toNat_and_mask21_lt _) (by norm_num) fun s7 hs7 hs7lo hs7hi => ?_
  refine digit_elim hv82 (toNat_and_mask21_lt _) (by norm_num) fun s8 hs8 hs8lo hs8hi => ?_
  refine digit_elim hv84 (toNat_and_mask21_lt _) (by norm_num) fun s9 hs9 hs9lo hs9hi => ?_
  refine digit_elim hv86 (toNat_and_mask21_lt _) (by norm_num) fun s10 hs10 hs10lo hs10hi => ?_
  refine digit_elim hv88 (toNat_and_mask21_lt _) (by norm_num) fun s11 hs11 hs11lo hs11hi => ?_
  refine digit_elim hv90 (toNat_and_mask21_lt _) (by norm_num) fun s12 hs12 hs12lo hs12hi => ?_
  refine digit_elim hv92 (toNat_and_mask21_lt _) (by norm_num) fun s13 hs13 hs13lo hs13hi => ?_
  refine digit_elim hv94 (toNat_and_mask21_lt _) (by norm_num) fun s14 hs14 hs14lo hs14hi => ?_
  refine digit_elim hv96 (toNat_and_mask21_lt _) (by norm_num) fun s15 hs15 hs15lo hs15hi => ?_
  refine digit_elim hv98 (toNat_and_mask21_lt _) (by norm_num) fun s16 hs16 hs16lo hs16hi => ?_
  refine digit_elim hv100 (toNat_and_mask21_lt _) (by norm_num) fun s17 hs17 hs17lo hs17hi => ?_
  refine digit_elim hv102 (toNat_and_mask21_lt _) (by norm_num) fun s18 hs18 hs18lo hs18hi => ?_
  refine digit_elim hv104 (toNat_and_mask21_lt _) (by norm_num) fun s19 hs19 hs19lo hs19hi => ?_
  refine digit_elim hv106 (toNat_and_mask21_lt _) (by norm_num) fun s20 hs20 hs20lo hs20hi => ?_
  refine digit_elim hv108 (toNat_and_mask21_lt _) (by norm_num) fun s21 hs21 hs21lo hs21hi => ?_
  refine digit_elim hv110 (toNat_and_mask21_lt _) (by norm_num) fun s22 hs22 hs22lo hs22hi => ?_
  refine digit_elim hv111 (toNat_shiftRight35_lt _) (by norm_num) fun s23 hs23 hs23lo hs23hi => ?_

  -- ## The first reduction row
  --
  -- `s11 += s23*666643; s12 += s23*470296; s13 += s23*654183;`
  -- `s14 -= s23*997805; s15 += s23*136657; s16 -= s23*683901; s23 = 0`
  --
  -- Twelve instructions, `%112`-`%123`, alternating `mul` by one of the six
  -- constants with an `add` into the running digit. `s23 = 0` is not an
  -- instruction: nothing reads `s23` again, so the compiler dropped it.
  --
  -- Every product is `s23 * c` with `0 ≤ s23 < 2^29` and `|c| ≤ 997805 < 2^20`,
  -- so `mul_range` closes each `nsw` at `A * C = 2^29 * 997805 < 2^63`.

  -- the six multipliers, as the signed integers the guards compare against
  have hc29 : (666643#64 : BitVec 64).toInt = 666643 := by decide
  have hc30 : (470296#64 : BitVec 64).toInt = 470296 := by decide
  have hc31 : (654183#64 : BitVec 64).toInt = 654183 := by decide
  have hc32 : ((-997805 : BitVec 64)).toInt = -997805 := by decide
  have hc33 : (136657#64 : BitVec 64).toInt = 136657 := by decide
  have hc34 : ((-683901 : BitVec 64)).toInt = -683901 := by decide

  sorry

end Firedancer.Common

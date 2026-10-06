import SSA.Projects.Agave.Ed25519.Bridge.Encoding

/-!
Field interpretation of the pinned `solana-ed25519` 0.2.4 decompression
square-root algorithm (`src/field.rs:160-193,295-303,343-363`). The addition
chain, both root corrections, the success flag, and the parity normalization
are represented explicitly. The concrete finite-field facts come from the
existing Firedancer development, not from assumptions about a decoder.

This file proves the mathematics of those source operations. The supplementary
`decompress-manifest.json` and `DecompressExecution` modules separately extract
and import the exact bodies. Their full execution refinement is still
outstanding; this is not an RIR execution-conformance theorem.
-/

namespace Agave.Ed25519.Encoding.Decompress

open _root_.Ed25519 Bridge

abbrev K := ZMod p

/-- The pinned serial D limbs denote the same curve coefficient. -/
theorem source_d_limbs :
    (((929955233495203 : Nat) + 466365720129213 * 2^51 +
      1662059464998953 * 2^102 + 2033849074728123 * 2^153 +
      1442794654840575 * 2^204 : Nat) : K) = d := by decide +kernel

/-- The pinned serial SQRT_M1 limbs denote the same even square root of -1. -/
theorem source_sqrtm1_limbs :
    (((1718705420411056 : Nat) + 234908883556509 * 2^51 +
      2233514472574048 * 2^102 + 2117202627021982 * 2^153 +
      765476049583133 * 2^204 : Nat) : K) = sqrtm1 := by decide +kernel

/-- The addition chain in `FieldElement::pow22501`. `pow2k(k)` is interpreted
as exponentiation by `2^k`; its machine loop is a separate refinement. -/
def pow22501 (x : K) : K × K :=
  let t0 := x ^ 2
  let t1 := (t0 ^ 2) ^ 2
  let t2 := x * t1
  let t3 := t0 * t2
  let t4 := t3 ^ 2
  let t5 := t2 * t4
  let t6 := t5 ^ (2 ^ 5)
  let t7 := t6 * t5
  let t8 := t7 ^ (2 ^ 10)
  let t9 := t8 * t7
  let t10 := t9 ^ (2 ^ 20)
  let t11 := t10 * t9
  let t12 := t11 ^ (2 ^ 10)
  let t13 := t12 * t7
  let t14 := t13 ^ (2 ^ 50)
  let t15 := t14 * t13
  let t16 := t15 ^ (2 ^ 100)
  let t17 := t16 * t15
  let t18 := t17 ^ (2 ^ 50)
  let t19 := t18 * t13
  (t19, t3)

theorem pow22501_eq (x : K) : pow22501 x = (x ^ (2 ^ 250 - 1), x ^ 11) := by
  apply Prod.ext <;>
    simp only [pow22501, ← pow_mul, ← pow_add, ← pow_succ'] <;> norm_num

/-- The final two squarings and multiplication in `FieldElement::pow_p58`. -/
def powP58 (x : K) : K := x * (pow22501 x).1 ^ (2 ^ 2)

theorem powP58_eq (x : K) : powP58 x = x ^ ((p - 5) / 8) := by
  simp only [powP58, pow22501_eq, ← pow_mul, ← pow_succ'] <;> norm_num [p]

/-- The exact order of square/multiply operations before the comparisons. -/
def candidate (u v : K) : K :=
  let v3 := v ^ 2 * v
  let v7 := v3 ^ 2 * v
  (u * v3) * powP58 (u * v7)

theorem candidate_eq (u v : K) :
    candidate u v = u * v ^ 3 * (u * v ^ 7) ^ ((p - 5) / 8) := by
  have h3 : v ^ 2 * v = v ^ 3 := by ring
  simp only [candidate, h3, powP58_eq]
  rw [show (v ^ 3) ^ 2 * v = v ^ 7 by ring]

def check (u v : K) : K := v * candidate u v ^ 2

/-- Both source comparisons participate in the root correction, including
the comparison only relevant to the nonsquare return value. -/
def correctedRoot (u v : K) : K :=
  if check u v = -u ∨ check u v = -u * sqrtm1 then
    sqrtm1 * candidate u v
  else candidate u v

/-- `is_negative` serializes canonically and tests the low bit. -/
def nonnegative (x : K) : K := if x.val % 2 = 1 then -x else x

theorem nonnegative_sq (x : K) : nonnegative x ^ 2 = x ^ 2 := by
  unfold nonnegative
  split <;> ring

theorem nonnegative_even (x : K) : (nonnegative x).val % 2 = 0 := by
  unfold nonnegative
  split
  · rename_i hodd
    have hx : x ≠ 0 := by
      intro hzero
      simp [hzero] at hodd
    rw [ZMod.neg_val, if_neg hx]
    have hlt := ZMod.val_lt x
    have hpos := (ZMod.val_ne_zero x).mpr hx
    have hp : p % 2 = 1 := by decide
    omega
  · have hlt := Nat.mod_lt x.val (by decide : 0 < 2)
    omega

private theorem sqrtm1_ne_neg_one : (sqrtm1 : K) ≠ -1 := by
  intro h
  have hs := sqrtm1_sq
  rw [h] at hs
  exact two_ne_zero (by linear_combination hs)

theorem correctedRoot_sq (u v : K)
    (hvalid : check u v = u ∨ check u v = -u) :
    correctedRoot u v ^ 2 * v = u := by
  by_cases hu : u = 0
  · subst u
    simp [correctedRoot, check, candidate]
  rcases hvalid with hcorrect | hflipped
  · have hno : ¬(check u v = -u ∨ check u v = -u * sqrtm1) := by
      rintro (hneg | himag)
      · have hz : (2 : K) * u = 0 := by linear_combination hneg - hcorrect
        exact hu ((mul_eq_zero.mp hz).resolve_left two_ne_zero)
      · have hz : u * (sqrtm1 + 1) = 0 := by
          linear_combination himag - hcorrect
        have hi := (mul_eq_zero.mp hz).resolve_left hu
        exact sqrtm1_ne_neg_one (by linear_combination hi)
    rw [correctedRoot, if_neg hno]
    simpa only [check, mul_comm] using hcorrect
  · rw [correctedRoot, if_pos (Or.inl hflipped)]
    calc
      (sqrtm1 * candidate u v) ^ 2 * v =
          sqrtm1 ^ 2 * check u v := by unfold check; ring
      _ = u := by rw [sqrtm1_sq, hflipped]; ring

/-- The source's `(was_nonzero_square, r)` result. Despite the flag's name,
the source accepts zero numerators, including `(u,v)=(0,0)`. -/
def sqrtRatio (u v : K) : Bool × K :=
  (decide (check u v = u ∨ check u v = -u), nonnegative (correctedRoot u v))

/-- Explicit projection rewrites prevent elaboration from reducing the
finite-field arithmetic while trying to infer a root from its `val`. -/
theorem sqrtRatio_fst (u v : K) :
    (sqrtRatio u v).1 = decide (check u v = u ∨ check u v = -u) := rfl

section
-- When both sides have the concrete finite-field type, unrestricted `rfl`
-- may unfold `nonnegative` before reducing the pair projection, exposing its
-- parity test and the complete exponentiation chain. Only the pair
-- constructor is relevant here, so keep the root computation opaque locally.
attribute [local irreducible] nonnegative

theorem sqrtRatio_snd (u v : K) :
    (sqrtRatio u v).2 = nonnegative (correctedRoot u v) := by
  unfold sqrtRatio
  rfl

end

theorem sqrtRatio_even (u v : K) : (sqrtRatio u v).2.val % 2 = 0 := by
  rw [sqrtRatio_snd]
  exact nonnegative_even (correctedRoot u v)

theorem sqrtRatio_root (u v : K) (hvalid : (sqrtRatio u v).1 = true) :
    (sqrtRatio u v).2 ^ 2 * v = u := by
  rw [sqrtRatio_snd, nonnegative_sq]
  apply correctedRoot_sq
  rw [sqrtRatio_fst] at hvalid
  exact of_decide_eq_true hvalid

theorem sqrtRatio_success_iff (u v : K) (hv : v ≠ 0) :
    (sqrtRatio u v).1 = true ↔ IsSquare (u / v) := by
  rw [sqrtRatio_fst, decide_eq_true_eq]
  simpa only [check, mul_comm] using sqrtCandidate_iff hv (candidate_eq u v)

theorem sqrtRatio_zero_numerator (v : K) : sqrtRatio 0 v = (true, 0) := by
  simp [sqrtRatio, check, correctedRoot, candidate, nonnegative]

theorem sqrtRatio_zero_denominator (u : K) :
    sqrtRatio u 0 = (decide (u = 0), 0) := by
  by_cases hu : u = 0
  · simp [hu, sqrtRatio_zero_numerator]
  · simp [sqrtRatio, check, correctedRoot, candidate, nonnegative, hu, Ne.symm hu]

/-- Unrestricted success/failure classification, including a zero denominator. -/
theorem sqrtRatio_success_iff_root (u v : K) :
    (sqrtRatio u v).1 = true ↔ ∃ x : K, x ^ 2 * v = u := by
  by_cases hv : v = 0
  · subst v
    simp [sqrtRatio_zero_denominator, eq_comm]
  · rw [sqrtRatio_success_iff u v hv, isSquare_div_iff hv]

end Agave.Ed25519.Encoding.Decompress

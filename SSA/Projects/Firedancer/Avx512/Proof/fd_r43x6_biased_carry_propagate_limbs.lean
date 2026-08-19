/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_biased_carry_propagate_limbs
import Mathlib.Data.ZMod.Basic

/-!
# `fd_r43x6_biased_carry_propagate_limbs` is a nearly reducing carry propagate

Two things are proved about `bcp`, at an arbitrary bias `b`, so that the nine
operations expanding this macro can each take what they need.

* **`decodeLimbs_bcp`, the value.** An exact integer identity with no
  hypothesis: the chain subtracts limb 5's overflow times `p` and nothing
  else. `2^255 ≡ 19 (mod p)`, the six masks and the bias all cancel into that
  one term, and `bcp_congr` is the corollary in `ZMod p`.

* **`bcp_limbs`, the range.** Under `BcpPre b`, the domain the header
  documents: limbs 0-4 come back in `[0,2^43)` and limb 5 in
  `[-2^20+b, 2^40+2^20-1+b)`. `bcp_chain_fitsLong` is the same argument read
  off the intermediates rather than the results -- no `long` in the chain
  overflows, which is what the emitted `nsw` flags need before the region
  denotes to a value at all.

Both are `omega` after `R43x6.shiftRight_eq`: with `>>>` as division the chain
is linear arithmetic over `ℤ` with division and remainder by literals, and the
carry bounds -- `x5 >> 40` in `[-2^23,2^23)`, each `>> 43` in `[-2^20,2^20)`
-- come out on the way.
-/

namespace Firedancer.Avx512

/-- The five limb hypotheses of `BcpPre` in the form the `omega` calls below
consume them. -/
private theorem BcpPre.limbs {b : ℤ} {x : Fin R43x6.limbCount → ℤ} (h : BcpPre b x) :
    (-2 ^ 63 + 19 * 2 ^ 23 ≤ x 0 ∧ x 0 < 2 ^ 63 - 19 * (2 ^ 23 - 1))
  ∧ (-2 ^ 63 + 2 ^ 20 ≤ x 1 ∧ x 1 < 2 ^ 63 - (2 ^ 20 - 1))
  ∧ (-2 ^ 63 + 2 ^ 20 ≤ x 2 ∧ x 2 < 2 ^ 63 - (2 ^ 20 - 1))
  ∧ (-2 ^ 63 + 2 ^ 20 ≤ x 3 ∧ x 3 < 2 ^ 63 - (2 ^ 20 - 1))
  ∧ (-2 ^ 63 + 2 ^ 20 ≤ x 4 ∧ x 4 < 2 ^ 63 - (2 ^ 20 - 1))
  ∧ (-2 ^ 63 + b ≤ x 5 ∧ x 5 < 2 ^ 63) :=
  ⟨h.1, h.2.1 1 (by decide) (by decide), h.2.1 2 (by decide) (by decide),
    h.2.1 3 (by decide) (by decide), h.2.1 4 (by decide) (by decide), h.2.2⟩

/-- The `s62` contract callers state, in terms of the six limbs of the
vector, implies the much wider domain the macro actually needs, for any bias
in `[0,2^20]`. `x.take 6` is the `fd_r43x6_t` proper: lanes 6 and 7 are
ignored, so nothing is said about them. -/
theorem bcpPre_of_s62 {b : ℤ} {x : Vector (BitVec 64) 8} (hb : 0 ≤ b)
    (hb' : b ≤ 2 ^ 20) (h : R43x6.S62 (x.take R43x6.limbCount)) :
    BcpPre b (R43x6.extractLimbs x) := by
  have key := R43x6.extractLimbs_bounds h
  have k0 := key 0; have k5 := key 5
  exact ⟨⟨by omega, by omega⟩,
    fun i _ _ => ⟨by have := key i; omega, by have := key i; omega⟩,
    by omega, by omega⟩

/-! ## The value

Limb 5's overflow `c5 = (x5 - b) >> 40` is the whole of the change: the chain
moves `2^255 c5` out of the top and `19 c5` back into limb 0, and
`2^255 - 19 = p`. -/

/-- **The carry propagate changes the packed value by exactly limb 5's
overflow times `p`.** No hypothesis: the identity holds for arbitrary limbs,
including ones the macro must not be applied to. -/
theorem decodeLimbs_bcp (b : ℤ) (x : Fin R43x6.limbCount → ℤ) :
    R43x6.decodeLimbs (bcp b x)
      = R43x6.decodeLimbs x - ((x 5 - b) >>> 40) * (p : ℤ) := by
  simp only [bcp, bcpA, R43x6.decodeLimbs_eq,
    R43x6.limbs6, R43x6.shiftRight_eq, p_int]
  omega

/-- **The element is preserved.** -/
theorem bcp_congr (b : ℤ) (x : Fin R43x6.limbCount → ℤ) :
    ((R43x6.decodeLimbs (bcp b x) : ℤ) : ZMod p)
      = ((R43x6.decodeLimbs x : ℤ) : ZMod p) :=
  intCast_eq_of_sub_mul (decodeLimbs_bcp b x)

/-! ## The range -/

/-- **The limbs the header promises**: limbs 0-4 fully carried, limb 5 within
one carry of `[b, 2^40+b)`. -/
theorem bcp_limbs {b : ℤ} {x : Fin R43x6.limbCount → ℤ} (hb : 0 ≤ b) (hb' : b ≤ 2 ^ 20)
    (h : BcpPre b x) :
    (∀ k : Fin R43x6.limbCount, (k : ℕ) < 5 → 0 ≤ bcp b x k ∧ bcp b x k < 2 ^ 43)
  ∧ (-2 ^ 20 + b ≤ bcp b x 5 ∧ bcp b x 5 < 2 ^ 40 + 2 ^ 20 - 1 + b) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h.limbs
  simp only [bcp, bcpA, R43x6.limbs6, R43x6.shiftRight_eq]
  refine ⟨fun k hk => ?_, ?_⟩
  · fin_cases k <;> simp_all <;> omega
  · simp; omega

/-- Every unmasked sum of the chain fits a `long`. -/
theorem bcpA_fitsLong {b : ℤ} {x : Fin R43x6.limbCount → ℤ} (hb : 0 ≤ b)
    (hb' : b ≤ 2 ^ 20) (h : BcpPre b x) (i : Fin R43x6.limbCount) :
    R43x6.FitsLong (bcpA b x i) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h.limbs
  simp only [R43x6.FitsLong, bcpA, R43x6.limbs6, R43x6.shiftRight_eq]
  fin_cases i <;> simp_all <;> omega

/-- The three values of the chain that are not one of the `bcpA i`: limb 5's
scaled overflow and the two partial sums that rebuild limb 5. -/
theorem bcp_aux_fitsLong {b : ℤ} {x : Fin R43x6.limbCount → ℤ} (hb : 0 ≤ b)
    (hb' : b ≤ 2 ^ 20) (h : BcpPre b x) :
    R43x6.FitsLong ((19 : ℤ) * (bcpA b x 5 >>> 40))
  ∧ R43x6.FitsLong (bcpA b x 5 % 2^40 + b)
  ∧ R43x6.FitsLong (bcpA b x 5 % 2^40 + b + (bcpA b x 4 >>> 43)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h.limbs
  simp only [R43x6.FitsLong, bcpA, R43x6.limbs6, R43x6.shiftRight_eq]
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- **No intermediate overflows a `long`.** The obligation behind the `nsw` on
every add, subtract and multiply of the emitted chain. -/
theorem bcp_chain_fitsLong {b : ℤ} {x : Fin R43x6.limbCount → ℤ} (hb : 0 ≤ b) (hb' : b ≤ 2 ^ 20)
    (h : BcpPre b x) : ∀ v ∈ bcpChain b x, R43x6.FitsLong v := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h.limbs
  intro v hv
  simp only [bcpChain, bcpA, R43x6.limbs6, R43x6.shiftRight_eq, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  simp only [R43x6.FitsLong]
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ## What the callers use -/

/-- **At `b = 2^20` a signed input comes back nearly reduced.** The bias is
what makes limb 5 non-negative: the last carry into it is as low as `-2^20`,
and `b` is exactly enough to absorb that. This is the form
`fd_r43x6_is_nonzero` and `fd_r43x6_diagnose` use. -/
theorem bcp_nearlyReduced {x : Fin R43x6.limbCount → ℤ} (h : BcpPre (2 ^ 20) x) :
    (∀ i : Fin R43x6.limbCount, (i : ℕ) < 5 → 0 ≤ bcp (2 ^ 20) x i ∧ bcp (2 ^ 20) x i < 2 ^ 43)
  ∧ 0 ≤ bcp (2 ^ 20) x 5
  ∧ R43x6.decodeLimbs (bcp (2 ^ 20) x) < 2 * (p : ℤ) := by
  obtain ⟨h04, h5⟩ := bcp_limbs (b := 2 ^ 20) (by norm_num) (by norm_num) h
  exact ⟨h04, by omega, R43x6.decodeLimbs_lt_two_p h04 (by omega) (by omega)⟩

/-- **At `b = 0` an unsigned input comes back nearly reduced too**, with the
tighter limb 5 the header records for that case. The form
`fd_r43x6_approx_mod_unsigned` and `fd_r43x6_fold_unsigned` need; it costs
only the observation that every carry out of a non-negative limb is
non-negative. -/
theorem bcp_nearlyReduced_of_unsigned {x : Fin R43x6.limbCount → ℤ}
    (h0 : 0 ≤ x 0 ∧ x 0 < 2 ^ 63 - 19 * (2 ^ 23 - 1))
    (h1 : 0 ≤ x 1 ∧ x 1 < 2 ^ 63 - (2 ^ 20 - 1))
    (h2 : 0 ≤ x 2 ∧ x 2 < 2 ^ 63 - (2 ^ 20 - 1))
    (h3 : 0 ≤ x 3 ∧ x 3 < 2 ^ 63 - (2 ^ 20 - 1))
    (h4 : 0 ≤ x 4 ∧ x 4 < 2 ^ 63 - (2 ^ 20 - 1))
    (h5 : 0 ≤ x 5 ∧ x 5 < 2 ^ 63) :
    (∀ i : Fin R43x6.limbCount, (i : ℕ) < 5 → 0 ≤ bcp 0 x i ∧ bcp 0 x i < 2 ^ 43)
  ∧ 0 ≤ bcp 0 x 5
  ∧ R43x6.decodeLimbs (bcp 0 x) < 2 * (p : ℤ) := by
  have h04 : ∀ k : Fin R43x6.limbCount, (k : ℕ) < 5 →
      0 ≤ bcp 0 x k ∧ bcp 0 x k < 2 ^ 43 := by
    intro k hk
    simp only [bcp, bcpA, R43x6.limbs6, R43x6.shiftRight_eq]
    fin_cases k <;> simp_all <;> omega
  have h5 : 0 ≤ bcp 0 x 5 ∧ bcp 0 x 5 < 2 ^ 40 + 2 ^ 21 - 1 := by
    simp only [bcp, bcpA, R43x6.limbs6, R43x6.shiftRight_eq]
    simp; omega
  exact ⟨h04, h5.1, R43x6.decodeLimbs_lt_two_p h04 h5.1 h5.2⟩

end Firedancer.Avx512

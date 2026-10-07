import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorNormalization

/-! Connect the exact word carry network to the integer carry32 schedule.
This includes the verifier's full Tight (<2^52) input range. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Normalization
open LeanMLIR.RIR Packing CacheArithmetic Avx2PointAdd Avx2PointAdd.Phases
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem low_shift (x : BitVec 64) : lowWord x >>> 26 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero]
  exact Nat.div_eq_of_lt (lowWord_bound x)

theorem low_mask (x : BitVec 64) : lowWord x &&& 67108863#32 = lowWord x := by
  simp only [lowWord, BitVec.and_assoc, BitVec.and_self]

theorem low_mod (x : BitVec 64) : (lowWord x).toNat % 67108864 = (lowWord x).toNat :=
  Nat.mod_eq_of_lt (lowWord_bound x)

theorem low_div (x : BitVec 64) : (lowWord x).toNat / 67108864 = 0 :=
  Nat.div_eq_of_lt (lowWord_bound x)

theorem mask25_word (x : BitVec 32) : x &&& 33554431#32 = word (x.toNat % 2^25) := by
  apply BitVec.eq_of_toNat_eq
  change x.toNat &&& (2^25-1) = x.toNat % 2^25 % 2^32
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by norm_num))]

theorem step_word (x y : BitVec 32) :
    (x >>> 25) + y = word (y.toNat + x.toNat / 2^25) := by
  apply BitVec.eq_of_toNat_eq
  simp [word, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.add_comm]

theorem top_toNat (x : BitVec 32) : (top x).toNat = x.toNat / 2^25 := by
  simp only [top, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (x.toNat / 2^25) &&& (2^7-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  have h := x.isLt
  norm_num at h ⊢
  omega

theorem first_word (x y : BitVec 32) :
    y + top x * 19#32 = word (y.toNat + 19 * (x.toNat / 2^25)) := by
  have h := x.isLt
  have hp : x.toNat / 2^25 * 19 < 2^32 := by norm_num at h ⊢; omega
  apply BitVec.eq_of_toNat_eq
  simp only [word, BitVec.toNat_add, BitVec.toNat_mul, top_toNat, BitVec.toNat_ofNat]
  change (y.toNat + (x.toNat / 2^25 * 19 % 2^32)) % 2^32 =
    (y.toNat + 19 * (x.toNat / 2^25)) % 2^32
  rw [Nat.mod_eq_of_lt hp, Nat.mul_comm]

/-- The parallel word network implements carry32 on the exact packing limbs.
No bound is required for this representation equation. -/
theorem blocks_point (a : SerialPoint) (k : Fin 5) :
    normalizedBlocks a k = packPoint (normalizedPoint a) k := by
  fin_cases k <;> apply Vector.ext
  all_goals intro i hi
  all_goals interval_cases i <;> simp [normalizedBlocks, first, masked, masks, fold,
    step, pack, packPoint, normalizedPoint, normalizedLimbs, carry32, limbs,
    Field.flatten, evenIndex, oddIndex, low_shift, low_mask, low_mod, low_div,
    mask25_word, step_word, first_word]

/-- Exact imported normalization output, now identified with the field-level
point schedule. All source operations and overflow flags remain in scope. -/
theorem network_point (E : ⟪kernel.Γ⟫) (a : SerialPoint) (k : Fin 5) :
    reads (CachePhases.normalizeResult (input E a)) k =
      Ty.wrap (packPoint (normalizedPoint a) k) := by
  rw [network, blocks_point]

/-- The true verifier input range suffices for every advertised output bound
and value of the exact constructor normalization interval. -/
theorem tight_normalization (E : ⟪kernel.Γ⟫) (a : SerialPoint)
    (ha : ∀ e k, (a e k).toNat < 2^52) :
    (∀ k, reads (CachePhases.normalizeResult (input E a)) k =
      Ty.wrap (packPoint (normalizedPoint a) k)) ∧
    pointReduced (normalizedPoint a) ∧
    pointValue (normalizedPoint a) = serialPointValue a :=
  ⟨network_point E a, normalized_reduced a ha, normalized_value a ha⟩

end Agave.Ed25519.Tables.Avx2Constructor.Normalization

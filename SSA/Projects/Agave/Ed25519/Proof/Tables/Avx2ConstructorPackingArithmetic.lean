import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorPacking

/-! Integer refinement of the constructor's first packing interval. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Packing
open LeanMLIR.RIR

set_option maxHeartbeats 1000000

theorem lowWord_toNat (x : BitVec 64) :
    (lowWord x).toNat = x.toNat % 2^26 := by
  change (x.toNat % 2^32) &&& (2^26 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd]
  decide

theorem highWord_toNat (x : BitVec 64) (hx : x.toNat < 2^51) :
    (highWord x).toNat = x.toNat / 2^26 := by
  simp only [highWord, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  norm_num at hx ⊢
  omega

theorem lowWord_bound (x : BitVec 64) : (lowWord x).toNat < 2^26 := by
  rw [lowWord_toNat]
  exact Nat.mod_lt _ (by decide)

theorem highWord_bound (x : BitVec 64) (hx : x.toNat < 2^51) :
    (highWord x).toNat < 2^25 := by
  rw [highWord_toNat x hx]
  norm_num at hx ⊢
  omega

theorem pack_low (a : SerialPoint) (e : Fin 4) (k : Fin 5) :
    (pack a k)[Field.evenLane e] = lowWord (a e k) := by
  fin_cases e <;> simp [pack, Field.evenLane]

theorem pack_high (a : SerialPoint) (e : Fin 4) (k : Fin 5) :
    (pack a k)[Field.oddLane e] = highWord (a e k) := by
  fin_cases e <;> simp [pack, Field.oddLane]

/-- Splitting a radix-51 coefficient preserves its whole integer value. -/
theorem pair_value (x : BitVec 64) (hx : x.toNat < 2^51) :
    (lowWord x).toNat + (highWord x).toNat * 2^26 = x.toNat := by
  rw [lowWord_toNat, highWord_toNat x hx]
  exact Nat.mod_add_div' _ _

/-- The constructor's physical SIMD lane ordering preserves every input
coordinate, with equality of integers before passage to the field. -/
theorem pack_value (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^51)
    (e : Fin 4) :
    Field.packedValue (fun k j => (pack a k)[j]) e = Field.serialValue (a e) := by
  unfold Field.packedValue
  rw [← Field.decode_pair]
  congr 1
  funext k
  simp only [Field.pair, Field.lo, Field.hi, pack_low, pack_high]
  exact pair_value (a e k) (ha e k)

def limbs (a : SerialPoint) (e : Fin 4) : Fin 10 → Nat :=
  Field.flatten (fun k => (lowWord (a e k)).toNat)
    (fun k => (highWord (a e k)).toNat)

/-- The original strict radix-51 input bound yields strict alternating
radix-26/25 output bounds, stronger than the point helper invariant. -/
theorem limbs_bound (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^51)
    (e : Fin 4) (i : Fin 10) :
    limbs a e i < 2^(if i.val % 2 = 0 then 26 else 25) := by
  unfold limbs Field.flatten
  split_ifs
  · exact lowWord_bound _
  · exact highWord_bound _ (ha _ _)

theorem limbs_reduced (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^51)
    (e : Fin 4) : Avx2PointAdd.reduced (limbs a e) := by
  intro i
  exact (limbs_bound a ha e i).trans_le (Nat.le_add_right _ _)

theorem limbs_value (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^51)
    (e : Fin 4) :
    Field.decode10 (limbs a e) = Field.serialValue (a e) := by
  unfold limbs
  rw [Field.decode_flatten, ← Field.decode_pair]
  congr 1
  funext k
  exact pair_value (a e k) (ha e k)

/-- The high-word truncation retains all bits through bit 57. In particular,
radix-51 limbs with one carry bit are not truncated by this packing stage. -/
theorem highWord_toNat_of_lt58 (x : BitVec 64) (hx : x.toNat < 2^58) :
    (highWord x).toNat = x.toNat / 2^26 := by
  simp only [highWord, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  norm_num at hx ⊢
  omega

theorem pair_value_of_lt58 (x : BitVec 64) (hx : x.toNat < 2^58) :
    (lowWord x).toNat + (highWord x).toNat * 2^26 = x.toNat := by
  rw [lowWord_toNat, highWord_toNat_of_lt58 x hx]
  exact Nat.mod_add_div' _ _

/-- This broader packing boundary includes the verifier's one-carry-bit
radix-51 limbs. Carry propagation happens in the following instruction phase. -/
theorem pack_value_of_lt58 (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^58)
    (e : Fin 4) :
    Field.packedValue (fun k j => (pack a k)[j]) e = Field.serialValue (a e) := by
  unfold Field.packedValue
  rw [← Field.decode_pair]
  congr 1
  funext k
  simp only [Field.pair, Field.lo, Field.hi, pack_low, pack_high]
  exact pair_value_of_lt58 (a e k) (ha e k)

theorem limbs_value_of_lt58 (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^58)
    (e : Fin 4) : Field.decode10 (limbs a e) = Field.serialValue (a e) := by
  unfold limbs
  rw [Field.decode_flatten, ← Field.decode_pair]
  congr 1
  funext k
  exact pair_value_of_lt58 (a e k) (ha e k)

/-- With a single serial carry bit, every packed word is still below 2^26. -/
theorem limbs_bound52 (a : SerialPoint) (ha : ∀ e k, (a e k).toNat < 2^52)
    (e : Fin 4) (i : Fin 10) : limbs a e i < 2^26 := by
  unfold limbs Field.flatten
  split_ifs
  · exact lowWord_bound _
  · dsimp only
    rw [highWord_toNat_of_lt58 _ (lt_trans (ha e ⟨i.val / 2, by omega⟩) (by norm_num))]
    have h := ha e ⟨i.val / 2, by omega⟩
    norm_num at h ⊢
    omega

end Agave.Ed25519.Tables.Avx2Constructor.Packing

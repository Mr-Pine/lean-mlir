import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkEntry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ContextContract

/-! Natural-number interpretation of the emitted parity, pair count, and cursor. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 100000

/-- At most one block is consumed by the scalar prologue. -/
theorem bulkParity_toNat (count : BitVec 64) :
    (bulkParity count).toNat = count.toNat % 2 := by
  simp [bulkParity, BitVec.toNat_and]

theorem bulkParity_eq (count : BitVec 64) :
    bulkParity count = BitVec.ofNat 64 (count.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [bulkParity_toNat]
  simp only [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by have := Nat.mod_lt count.toNat (by decide : 0 < 2); omega)).symm

theorem bulk_count_split (n : Nat) : n % 2 + 2 * (n / 2) = n := by omega

theorem bulk_pair_cursor (n j : Nat) (hj : j ≤ n / 2) :
    n % 2 + 2 * j + 2 * (n / 2 - j) = n := by omega

theorem bulk_pair_live_index (n j : Nat) (hj : j < n / 2) :
    n % 2 + 2 * j + 2 ≤ n := by omega

private theorem bulk_ofNat_toNat (n : Nat) (hn : n < 2^64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hn

/-- No unsigned saturation is taken when subtracting an already consumed prefix. -/
theorem bulk_usub (n consumed : Nat) (hn : n < 2^64) (hc : consumed ≤ n) :
    Operation.usubSat (.value (BitVec.ofNat 64 n)) (.value (BitVec.ofNat 64 consumed)) =
      .value (BitVec.ofNat 64 (n-consumed)) := by
  have hcons : consumed < 2^64 := by omega
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 consumed = BitVec.ofNat 64 (n-consumed) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · simp only [bulk_ofNat_toNat n hn, bulk_ofNat_toNat consumed hcons,
        bulk_ofNat_toNat (n-consumed) (by omega)]
    · simpa only [BitVec.le_def, bulk_ofNat_toNat n hn, bulk_ofNat_toNat consumed hcons] using hc
  simp [Operation.usubSat, BitVec.ult_eq_decide, bulk_ofNat_toNat n hn,
    bulk_ofNat_toNat consumed hcons, Nat.not_lt.mpr hc, hsub]

/-- The emitted shift divides the even remaining block count by two. -/
theorem bulk_half (pairs : Nat) (hp : 2*pairs < 2^64) :
    Operation.lshr false (.value (BitVec.ofNat 64 (2*pairs))) (.value 1#64) =
      .value (BitVec.ofNat 64 pairs) := by
  have hv : BitVec.ofNat 64 (2*pairs) >>> (1 : Nat) = BitVec.ofNat 64 pairs := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, bulk_ofNat_toNat (2*pairs) hp,
      bulk_ofNat_toNat pairs (by omega), Nat.shiftRight_eq_div_pow]
    omega
  simpa [Operation.lshr] using congrArg LeanMLIR.RIR.PoisonOr.value hv

/-- The signed-no-overflow subtraction is valid for the live input count bound. -/
theorem bulk_pair_sub (pairs : Nat) (hp : 2*pairs < 2^56) :
    Operation.sub {nsw := true} (.value (BitVec.ofNat 64 (2*pairs)))
      (.value (BitVec.ofNat 64 pairs)) = .value (BitVec.ofNat 64 pairs) := by
  have h2 : (BitVec.ofNat 64 (2*pairs)).toNat = 2*pairs := bulk_ofNat_toNat _ (by omega)
  have h1 : (BitVec.ofNat 64 pairs).toNat = pairs := bulk_ofNat_toNat _ (by omega)
  have hi2 : (BitVec.ofNat 64 (2*pairs)).toInt = (2*pairs : Nat) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [h2]; omega), h2]
  have hi1 : (BitVec.ofNat 64 pairs).toInt = (pairs : Nat) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [h1]; omega), h1]
  have hov : (BitVec.ofNat 64 (2*pairs)).ssubOverflow (BitVec.ofNat 64 pairs) = false := by
    simp only [BitVec.ssubOverflow, hi2, hi1]
    norm_num
    omega
  have heq : BitVec.ofNat 64 (2*pairs) - BitVec.ofNat 64 pairs = BitVec.ofNat 64 pairs := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · rw [h2, h1]; omega
    · rw [BitVec.le_def, h1, h2]; omega
  simp [Operation.sub, hov, heq]

/-- Counter updates correspond to one pair consumed and one pair remaining less. -/
theorem bulk_counter_decrement (pairs : Nat) (hp : 0 < pairs) (_hb : pairs < 2^64) :
    BitVec.ofNat 64 pairs + 18446744073709551615#64 = BitVec.ofNat 64 (pairs-1) := by
  have hneg : (18446744073709551615#64) = -1#64 := by decide
  rw [hneg, ← BitVec.sub_eq_add_neg]
  exact BitVec.ofNat_sub_ofNat_of_le pairs 1 (by decide) hp

theorem bulk_counter_nonzero (pairs : Nat) (hp : 1 < pairs) (hb : pairs < 2^64) :
    BitVec.ofNat 64 pairs + 18446744073709551615#64 ≠ 0#64 := by
  rw [bulk_counter_decrement pairs (by omega) hb]
  intro heq
  have hh := congrArg BitVec.toNat heq
  simp only [bulk_ofNat_toNat (pairs-1) (by omega), BitVec.toNat_ofNat] at hh
  omega

theorem bulk_index_increment (index : Nat) :
    BitVec.ofNat 64 index + 2#64 = BitVec.ofNat 64 (index+2) :=
  (BitVec.ofNat_add index 2).symm

end Agave.Ed25519.SHA512.Execution.Avx2

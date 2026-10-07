import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Contracts

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.SHA512

/-- The emitted length arithmetic is wrapping, including contexts with a
block count at or above 2^118. The digest padding definition uses the same
modulo-2^128 length field; no additional bound on completed input is needed. -/
theorem bitLength_wrapping (blocks : BitVec 128) (pending : BitVec 8)
    (hp : pending.toNat < 128) :
    ((blocks <<< 10) ||| (pending.setWidth 128 <<< 3)) =
      BitVec.ofNat 128 (8 * (128 * blocks.toNat + pending.toNat)) := by
  have hshift : blocks <<< 10 = (blocks.setWidth 118).setWidth 128 <<< 10 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    omega
  have hblocks : ((blocks.setWidth 118).setWidth 128).toNat < 2 ^ 118 := by
    simp only [BitVec.toNat_setWidth]
    have := Nat.mod_lt blocks.toNat (by decide : 0 < 2 ^ 118)
    omega
  rw [hshift, bitLength_arithmetic _ pending hblocks hp]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

/-- The nonnegative extension flag follows from the context's residual count. -/
theorem pending_zext128 (pending : BitVec 8) (hp : pending.toNat < 128) :
    Operation.zext true (.value pending) =
      (.value (pending.setWidth 128) : PoisonOr (BitVec 128)) := by
  have hm : pending.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    omega
  simp [Operation.zext, hm]

theorem pending_zext64 (pending : BitVec 8) (hp : pending.toNat < 128) :
    Operation.zext true (.value pending) =
      (.value (pending.setWidth 64) : PoisonOr (BitVec 64)) := by
  have hm : pending.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    omega
  simp [Operation.zext, hm]

/-- Both no-overflow flags on the pending-byte shift hold even for the full
u8 domain, since the shift occurs after extension to 128 bits. -/
theorem pending_shift (pending : BitVec 8) :
    Operation.shl { nsw := true, nuw := true }
      (.value (pending.setWidth 128)) (.value 3#128) =
      .value (pending.setWidth 128 <<< 3) := by
  have hp := pending.isLt
  have hu : (pending.setWidth 128 <<< 3) >>> 3 = pending.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  have hm : (pending.setWidth 128 <<< 3).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    omega
  have hs : (pending.setWidth 128 <<< 3).sshiftRight 3 = pending.setWidth 128 := by
    rw [BitVec.sshiftRight_eq_of_msb_false hm, hu]
  simp [Operation.shl, hu, hs]

/-- The shifted complete-block and residual counts occupy disjoint bits. -/
theorem bitLength_disjoint (blocks : BitVec 128) (pending : BitVec 8)
    (hp : pending.toNat < 128) :
    (blocks <<< 10) &&& (pending.setWidth 128 <<< 3) = 0 := by
  have hsmall : pending.setWidth 128 = (pending.setWidth 7).setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega
  rw [hsmall]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi128
  by_cases hi : i < 10
  · simp [BitVec.getLsbD_shiftLeft, hi]
  · have hj : ¬ i - 3 < 7 := by omega
    simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hj]

/-- The imported disjoint OR is defined, not merely arithmetically equal
when poison/undefined execution is ignored. -/
theorem bitLength_or_defined (blocks : BitVec 128) (pending : BitVec 8)
    (hp : pending.toNat < 128) :
    Operation.or true (.value (blocks <<< 10)) (.value (pending.setWidth 128 <<< 3)) =
      .value (BitVec.ofNat 128 (8 * (128 * blocks.toNat + pending.toNat))) := by
  simp [Operation.or, bitLength_disjoint blocks pending hp, bitLength_wrapping blocks pending hp]

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
